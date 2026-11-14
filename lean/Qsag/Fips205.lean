module
/-
# Qsag.Fips205 — Exact NIST FIPS 205 Stateless Hash-Based Signatures (All 6 `SLH-DSA-SHAKE` Sets)

Self-contained Lean 4.35 specification and soundness proofs for all 6 NIST FIPS 205 (August 2024)
`SLH-DSA-SHAKE` parameter sets (`128s`: `7,856`B, `128f`: `17,088`B, `192s`: `16,224`B,
`192f`: `35,664`B, `256s`: `29,792`B, `256f`: `49,856`B):
1. Exact 32-byte big-endian `Fips205Adrs` (`>IIQIIII`: `layer` 4B, `tree` 12B, `type` 4B,
   `kp` 4B, `f5` 4B, `f6` 4B) and injectivity (`encodeFips205Adrs_injective`).
2. Exact §11.2.1 `SHAKE256` tweakable hash functions (`PRF_msg`, `H_msg`, `PRF`, `F`, `H`, `T_ℓ`)
   without extra length prefixes so wire outputs match NIST ACVP & OpenSSL 3.5 byte-for-byte.
3. Exact Algorithm 4 `base_2b`, Algorithm 6 WOTS+ ($w = 16, \ell_1 = 32, \ell_2 = 3, \ell = 35$)
   digit + shifted-checksum encoding, and checksum incomparability theorem
   (`fips205_wots_incomparable_no_chain_forgery`).
4. Exact Algorithm 9 `xmss_node` (`kp = 0`), Algorithm 15 `fors_node` (`kp = idx_leaf`),
   Algorithm 19 `slh_sign_internal`, Algorithm 20 `slh_verify_internal`, pure `slh_sign` /
   `slh_verify` (`0x00 || |ctx| || ctx || M`), and exact `17,088`B / `7,856`B wire codecs.
5. Unconditional completeness (`slhVerifyInternal_slhSignInternal`) and threshold-to-standard
   signature bit-identity (`thresholdSlhSign_eq_slhSignInternal`).
-/

public import Qsag.Keccak
public import Qsag.Tactic.AssuranceKit

public section
namespace Qsag

set_option autoImplicit false

/-! ## 1. Exact NIST FIPS 205 §4.2 32-Byte Address (`Fips205Adrs`) -/

/-- NIST FIPS 205 Table 1 address types (`0..6`). -/
inductive FipsAdrsType where
  | wotsHash  -- 0: WOTS_HASH
  | wotsPk    -- 1: WOTS_PK
  | tree      -- 2: TREE
  | forsTree  -- 3: FORS_TREE
  | forsRoots -- 4: FORS_ROOTS
  | wotsPrf   -- 5: WOTS_PRF
  | forsPrf   -- 6: FORS_PRF
  deriving DecidableEq, Repr, Inhabited

def FipsAdrsType.toCode : FipsAdrsType → Nat
  | .wotsHash  => 0
  | .wotsPk    => 1
  | .tree      => 2
  | .forsTree  => 3
  | .forsRoots => 4
  | .wotsPrf   => 5
  | .forsPrf   => 6

theorem FipsAdrsType.toCode_lt (t : FipsAdrsType) : t.toCode < 256 ^ 4 := by
  cases t <;> decide

theorem FipsAdrsType.toCode_injective {a b : FipsAdrsType} (h : a.toCode = b.toCode) : a = b := by
  cases a <;> cases b <;> simp [FipsAdrsType.toCode] at h <;> rfl

/-- Exact 32-byte NIST FIPS 205 `ADRS` (`layer`: 4B, `tree`: 12B, `adrsType`: 4B, `kp`: 4B, `f5`: 4B, `f6`: 4B). -/
structure Fips205Adrs where
  layer    : Nat
  tree     : Nat
  adrsType : FipsAdrsType
  kp       : Nat
  f5       : Nat
  f6       : Nat
  hLayer   : layer < 256 ^ 4 := by decide
  hTree    : tree < 256 ^ 12 := by decide
  hKp      : kp < 256 ^ 4 := by decide
  hF5      : f5 < 256 ^ 4 := by decide
  hF6      : f6 < 256 ^ 4 := by decide
  deriving DecidableEq, Repr

theorem Fips205Adrs.ext_fields {a b : Fips205Adrs}
    (h1 : a.layer = b.layer) (h2 : a.tree = b.tree) (h3 : a.adrsType = b.adrsType)
    (h4 : a.kp = b.kp) (h5 : a.f5 = b.f5) (h6 : a.f6 = b.f6) :
    a = b := by
  cases a; cases b; simp only at *; subst h1 h2 h3 h4 h5 h6; rfl

@[expose] def encodeFips205Adrs (a : Fips205Adrs) : List UInt8 :=
  be 4 a.layer ++ (be 12 a.tree ++ (be 4 a.adrsType.toCode ++
    (be 4 a.kp ++ (be 4 a.f5 ++ be 4 a.f6))))

@[simp] theorem encodeFips205Adrs_length (a : Fips205Adrs) :
    (encodeFips205Adrs a).length = 32 := by
  simp [encodeFips205Adrs, length_be]

theorem encodeFips205Adrs_injective {a b : Fips205Adrs}
    (h : encodeFips205Adrs a = encodeFips205Adrs b) : a = b := by
  unfold encodeFips205Adrs at h
  obtain ⟨h1, r1⟩ := List.append_inj h (by simp [length_be])
  obtain ⟨h2, r2⟩ := List.append_inj r1 (by simp [length_be])
  obtain ⟨h3, r3⟩ := List.append_inj r2 (by simp [length_be])
  obtain ⟨h4, r4⟩ := List.append_inj r3 (by simp [length_be])
  obtain ⟨h5, h6⟩ := List.append_inj r4 (by simp [length_be])
  exact Fips205Adrs.ext_fields
    (be_injective a.hLayer b.hLayer h1)
    (be_injective a.hTree b.hTree h2)
    (FipsAdrsType.toCode_injective (be_injective a.adrsType.toCode_lt b.adrsType.toCode_lt h3))
    (be_injective a.hKp b.hKp h4)
    (be_injective a.hF5 b.hF5 h5)
    (be_injective a.hF6 b.hF6 h6)

def mkFipsAdrs (layer tree : Nat) (ty : FipsAdrsType) (kp f5 f6 : Nat) : Fips205Adrs :=
  { layer    := layer % (256 ^ 4)
    tree     := tree % (256 ^ 12)
    adrsType := ty
    kp       := kp % (256 ^ 4)
    f5       := f5 % (256 ^ 4)
    f6       := f6 % (256 ^ 4)
    hLayer   := Nat.mod_lt _ (by decide)
    hTree    := Nat.mod_lt _ (by decide)
    hKp      := Nat.mod_lt _ (by decide)
    hF5      := Nat.mod_lt _ (by decide)
    hF6      := Nat.mod_lt _ (by decide) }

/-! ## 2. Exact NIST FIPS 205 Table 2 Parameter Sets & §11.2.1 `SHAKE256` Functions -/

/-- NIST FIPS 205 parameter record ($w = 16, \ell_1 = 2n, \ell_2 = 3, \ell = 2n + 3$). -/
structure Fips205Params where
  n        : Nat  -- Security parameter in bytes (`16` for 128-bit category 1)
  h        : Nat  -- Total hypertree height (`66` for 128f, `63` for 128s)
  d        : Nat  -- Hypertree layers (`22` for 128f, `7` for 128s)
  hp       : Nat  -- Subtree height `h' = h / d` (`3` for 128f, `9` for 128s)
  a        : Nat  -- FORS subtree height (`6` for 128f, `12` for 128s)
  k        : Nat  -- Number of FORS trees (`33` for 128f, `14` for 128s)
  m        : Nat  -- `H_msg` output bytes (`34` for 128f, `30` for 128s)
  deriving DecidableEq, Repr

def Fips205Params.ell1 (p : Fips205Params) : Nat := 2 * p.n
def Fips205Params.ell2 (_ : Fips205Params) : Nat := 3
def Fips205Params.ell  (p : Fips205Params) : Nat := 2 * p.n + 3
def Fips205Params.mdBytes (p : Fips205Params) : Nat := (p.k * p.a + 7) / 8
def Fips205Params.treeBytes (p : Fips205Params) : Nat := (p.h - p.hp + 7) / 8
def Fips205Params.leafBytes (p : Fips205Params) : Nat := (p.hp + 7) / 8
def Fips205Params.sigBytes (p : Fips205Params) : Nat :=
  p.n + p.k * (1 + p.a) * p.n + p.d * (p.ell + p.hp) * p.n

def Fips205Params.wellFormed (p : Fips205Params) : Bool :=
  decide (0 < p.n) && decide (p.n ≤ 32) &&
  decide (0 < p.d) && decide (p.h = p.d * p.hp) &&
  decide (0 < p.k) && decide (0 < p.a) &&
  decide (p.mdBytes + p.treeBytes + p.leafBytes ≤ p.m)

/-- Official NIST FIPS 205 `SLH-DSA-SHAKE-128f` (`PK = 32B, SK = 64B, SIG = 17,088B`). -/
@[expose] def slhDsaShake128f : Fips205Params :=
  { n := 16, h := 66, d := 22, hp := 3, a := 6, k := 33, m := 34 }

/-- Official NIST FIPS 205 `SLH-DSA-SHAKE-128s` (`PK = 32B, SK = 64B, SIG = 7,856B`). -/
@[expose] def slhDsaShake128s : Fips205Params :=
  { n := 16, h := 63, d := 7, hp := 9, a := 12, k := 14, m := 30 }

/-- Official NIST FIPS 205 `SLH-DSA-SHAKE-192f` (`PK = 48B, SK = 96B, SIG = 35,664B`). -/
def slhDsaShake192f : Fips205Params :=
  { n := 24, h := 66, d := 22, hp := 3, a := 8, k := 33, m := 42 }

/-- Official NIST FIPS 205 `SLH-DSA-SHAKE-192s` (`PK = 48B, SK = 96B, SIG = 16,224B`). -/
def slhDsaShake192s : Fips205Params :=
  { n := 24, h := 63, d := 7, hp := 9, a := 14, k := 17, m := 39 }

/-- Official NIST FIPS 205 `SLH-DSA-SHAKE-256f` (`PK = 64B, SK = 128B, SIG = 49,856B`). -/
def slhDsaShake256f : Fips205Params :=
  { n := 32, h := 68, d := 17, hp := 4, a := 9, k := 35, m := 49 }

/-- Official NIST FIPS 205 `SLH-DSA-SHAKE-256s` (`PK = 64B, SK = 128B, SIG = 29,792B`). -/
def slhDsaShake256s : Fips205Params :=
  { n := 32, h := 64, d := 8, hp := 8, a := 14, k := 22, m := 47 }

/-- Compact structural test profile (`n = 16, d = 2, hp = 2, h = 4, a = 2, k = 4, m = 4`). -/
def slhDsaShakeCompactTest : Fips205Params :=
  { n := 16, h := 4, d := 2, hp := 2, a := 2, k := 4, m := 3 }

theorem slhDsaShake128f_sigBytes : slhDsaShake128f.sigBytes = 17088 := by decide
theorem slhDsaShake128s_sigBytes : slhDsaShake128s.sigBytes = 7856 := by decide
theorem slhDsaShake192f_sigBytes : slhDsaShake192f.sigBytes = 35664 := by unfold slhDsaShake192f; decide
theorem slhDsaShake192s_sigBytes : slhDsaShake192s.sigBytes = 16224 := by unfold slhDsaShake192s; decide
theorem slhDsaShake256f_sigBytes : slhDsaShake256f.sigBytes = 49856 := by unfold slhDsaShake256f; decide
theorem slhDsaShake256s_sigBytes : slhDsaShake256s.sigBytes = 29792 := by unfold slhDsaShake256s; decide
theorem slhDsaShake128f_wellFormed : slhDsaShake128f.wellFormed = true := by decide
theorem slhDsaShake128s_wellFormed : slhDsaShake128s.wellFormed = true := by decide
theorem slhDsaShake192f_wellFormed : slhDsaShake192f.wellFormed = true := by unfold slhDsaShake192f; decide
theorem slhDsaShake192s_wellFormed : slhDsaShake192s.wellFormed = true := by unfold slhDsaShake192s; decide
theorem slhDsaShake256f_wellFormed : slhDsaShake256f.wellFormed = true := by unfold slhDsaShake256f; decide
theorem slhDsaShake256s_wellFormed : slhDsaShake256s.wellFormed = true := by unfold slhDsaShake256s; decide

/-- §11.2.1 `PRF_msg(SK.prf, opt_rand, M') = SHAKE256(SK.prf || opt_rand || M', 8n)`. -/
def fipsPrfMsg (n : Nat) (skPrf optRand msgPrime : List UInt8) : List UInt8 :=
  shake256Xof n (skPrf ++ optRand ++ msgPrime)

/-- §11.2.1 `H_msg(R, PK.seed, PK.root, M') = SHAKE256(R || PK.seed || PK.root || M', 8m)`. -/
def fipsHMsg (m : Nat) (rRand pkSeed pkRoot msgPrime : List UInt8) : List UInt8 :=
  shake256Xof m (rRand ++ pkSeed ++ pkRoot ++ msgPrime)

/-- §11.2.1 `PRF(PK.seed, SK.seed, ADRS) = SHAKE256(PK.seed || ADRS || SK.seed, 8n)`. -/
def fipsPrf (n : Nat) (pkSeed skSeed : List UInt8) (adrs : Fips205Adrs) : List UInt8 :=
  shake256Xof n (pkSeed ++ encodeFips205Adrs adrs ++ skSeed)

/-- §11.2.1 `F(PK.seed, ADRS, M_1) = SHAKE256(PK.seed || ADRS || M_1, 8n)`. -/
def fipsF (n : Nat) (pkSeed : List UInt8) (adrs : Fips205Adrs) (m1 : List UInt8) : List UInt8 :=
  shake256Xof n (pkSeed ++ encodeFips205Adrs adrs ++ m1)

/-- §11.2.1 `H(PK.seed, ADRS, M_1 || M_2) = SHAKE256(PK.seed || ADRS || M_1 || M_2, 8n)`. -/
def fipsH (n : Nat) (pkSeed : List UInt8) (adrs : Fips205Adrs) (m1 m2 : List UInt8) : List UInt8 :=
  shake256Xof n (pkSeed ++ encodeFips205Adrs adrs ++ m1 ++ m2)

/-- §11.2.1 `T_ℓ(PK.seed, ADRS, M) = SHAKE256(PK.seed || ADRS || M, 8n)`. -/
def fipsTl (n : Nat) (pkSeed : List UInt8) (adrs : Fips205Adrs) (ms : List (List UInt8)) : List UInt8 :=
  shake256Xof n (pkSeed ++ encodeFips205Adrs adrs ++ ms.flatten)

@[simp] theorem fipsPrf_length (n : Nat) (pkSeed skSeed : List UInt8) (adrs : Fips205Adrs) :
    (fipsPrf n pkSeed skSeed adrs).length = n := shake256Xof_length n _
@[simp] theorem fipsF_length (n : Nat) (pkSeed : List UInt8) (adrs : Fips205Adrs) (m1 : List UInt8) :
    (fipsF n pkSeed adrs m1).length = n := shake256Xof_length n _
@[simp] theorem fipsH_length (n : Nat) (pkSeed : List UInt8) (adrs : Fips205Adrs) (m1 m2 : List UInt8) :
    (fipsH n pkSeed adrs m1 m2).length = n := shake256Xof_length n _
@[simp] theorem fipsTl_length (n : Nat) (pkSeed : List UInt8) (adrs : Fips205Adrs) (ms : List (List UInt8)) :
    (fipsTl n pkSeed adrs ms).length = n := shake256Xof_length n _

theorem fipsPrfMsg_eq (n : Nat) (skPrf optRand msgPrime : List UInt8) :
    fipsPrfMsg n skPrf optRand msgPrime = shake256Xof n (skPrf ++ optRand ++ msgPrime) := by rfl
theorem fipsPrf_eq (n : Nat) (pkSeed skSeed : List UInt8) (adrs : Fips205Adrs) :
    fipsPrf n pkSeed skSeed adrs = shake256Xof n (pkSeed ++ encodeFips205Adrs adrs ++ skSeed) := by rfl
theorem fipsF_eq (n : Nat) (pkSeed : List UInt8) (adrs : Fips205Adrs) (m1 : List UInt8) :
    fipsF n pkSeed adrs m1 = shake256Xof n (pkSeed ++ encodeFips205Adrs adrs ++ m1) := by rfl

/-! ## 3. Exact Algorithm 4 `base_2b` & WOTS+ ($w = 16$) Incomparability Theorem -/

/-- Extract the `bitIdx`-th MSB-first bit from `bytes` (`bit 0` = MSB `(bytes[0] >>> 7) & 1`). -/
def msbBitAt (bytes : List UInt8) (bitIdx : Nat) : Nat :=
  let byteVal := (bytes.getD (bitIdx / 8) 0).toNat
  let shift := 7 - (bitIdx % 8)
  (byteVal / (2 ^ shift)) % 2

/-- NIST FIPS 205 Algorithm 4 `base_2b(X, b, out_len)`: MSB-first `b`-bit integer stream. -/
@[expose] def base2b (bytes : List UInt8) (b outLen : Nat) : List Nat :=
  (List.range outLen).map fun idx =>
    (List.range b).foldl (fun acc bitOff =>
      acc * 2 + msbBitAt bytes (idx * b + bitOff)) 0

theorem base2b_bounds (bytes : List UInt8) (b outLen : Nat) :
    (base2b bytes b outLen).length = outLen ∧
    ∀ d ∈ base2b bytes b outLen, d < 2 ^ b := by
  refine ⟨by simp [base2b], ?_⟩
  intro d hd
  simp only [base2b, List.mem_map] at hd
  obtain ⟨idx, _, rfl⟩ := hd
  suffices hFold : ∀ (w acc : Nat) (start : Nat),
      (List.range w).foldl (fun a bitOff => a * 2 + msbBitAt bytes (start + bitOff)) acc <
        (acc + 1) * 2 ^ w by
    have h0 := hFold b 0 (idx * b)
    simpa using h0
  intro w
  induction w with
  | zero => intro acc _; simp
  | succ w ih =>
    intro acc start
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hPrev := ih acc start
    have hBit : msbBitAt bytes (start + w) < 2 := Nat.mod_lt _ (by decide)
    rw [Nat.pow_succ, ← Nat.mul_assoc]
    omega

/-- Exact high/low 4-bit nibble expansion of a byte list (`b = 4`, `outLen = 2 * bytes.length`). -/
def byteNibbles : List UInt8 → List Nat
  | [] => []
  | x :: xs => (x.toNat / 16) :: (x.toNat % 16) :: byteNibbles xs

theorem byteNibbles_length (xs : List UInt8) : (byteNibbles xs).length = 2 * xs.length := by
  induction xs with
  | nil => rfl
  | cons _ xs ih => simp [byteNibbles, ih]; omega

theorem byteNibbles_injective : ∀ {xs ys : List UInt8},
    byteNibbles xs = byteNibbles ys → xs = ys
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [byteNibbles] at h
  | _ :: _, [], h => by simp [byteNibbles] at h
  | x :: xs, y :: ys, h => by
    simp only [byteNibbles, List.cons.injEq] at h
    rcases h with ⟨hHi, hLo, hRest⟩
    have hx := x.toNat_lt
    have hy := y.toNat_lt
    have hEqNat : x.toNat = y.toNat := by omega
    rw [UInt8.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq hEqNat), byteNibbles_injective hRest]

private theorem msbNibble_eq (bytes : List UInt8) (idx : Nat) (hLt : idx / 2 < bytes.length) :
    (List.range 4).foldl (fun acc bitOff => acc * 2 + msbBitAt bytes (idx * 4 + bitOff)) 0 =
      if idx % 2 = 0 then (bytes[idx / 2]'hLt).toNat / 16
      else (bytes[idx / 2]'hLt).toNat % 16 := by
  have hGetD : bytes.getD (idx / 2) 0 = bytes[idx / 2]'hLt := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hLt]; rfl
  have hbLt : (bytes[idx / 2]'hLt).toNat < 256 := (bytes[idx / 2]'hLt).toNat_lt
  have hr4 : List.range 4 = [0, 1, 2, 3] := rfl
  rw [hr4]
  by_cases hEven : idx % 2 = 0
  · have hDiv0 : (idx * 4 + 0) / 8 = idx / 2 := by omega
    have hDiv1 : (idx * 4 + 1) / 8 = idx / 2 := by omega
    have hDiv2 : (idx * 4 + 2) / 8 = idx / 2 := by omega
    have hDiv3 : (idx * 4 + 3) / 8 = idx / 2 := by omega
    have hMod0 : (idx * 4 + 0) % 8 = 0 := by omega
    have hMod1 : (idx * 4 + 1) % 8 = 1 := by omega
    have hMod2 : (idx * 4 + 2) % 8 = 2 := by omega
    have hMod3 : (idx * 4 + 3) % 8 = 3 := by omega
    simp only [List.foldl_cons, List.foldl_nil, msbBitAt, hDiv0, hDiv1, hDiv2, hDiv3,
               hMod0, hMod1, hMod2, hMod3, hGetD, hEven, ↓reduceIte]
    omega
  · have hDiv0 : (idx * 4 + 0) / 8 = idx / 2 := by omega
    have hDiv1 : (idx * 4 + 1) / 8 = idx / 2 := by omega
    have hDiv2 : (idx * 4 + 2) / 8 = idx / 2 := by omega
    have hDiv3 : (idx * 4 + 3) / 8 = idx / 2 := by omega
    have hMod0 : (idx * 4 + 0) % 8 = 4 := by omega
    have hMod1 : (idx * 4 + 1) % 8 = 5 := by omega
    have hMod2 : (idx * 4 + 2) % 8 = 6 := by omega
    have hMod3 : (idx * 4 + 3) % 8 = 7 := by omega
    simp only [List.foldl_cons, List.foldl_nil, msbBitAt, hDiv0, hDiv1, hDiv2, hDiv3,
               hMod0, hMod1, hMod2, hMod3, hGetD, hEven, ↓reduceIte]
    omega

private theorem byteNibbles_getElem : ∀ (xs : List UInt8) (idx : Nat) (h : idx < (byteNibbles xs).length),
    (byteNibbles xs)[idx]'h =
      if idx % 2 = 0 then (xs[idx / 2]'(by have := byteNibbles_length xs; omega)).toNat / 16
      else (xs[idx / 2]'(by have := byteNibbles_length xs; omega)).toNat % 16
  | [], idx, h => by simp [byteNibbles] at h
  | x :: xs, 0, _ => by simp [byteNibbles]
  | x :: xs, 1, _ => by simp [byteNibbles]
  | x :: xs, idx + 2, h => by
    have hLen : idx < (byteNibbles xs).length := by simp [byteNibbles] at h; omega
    have ih := byteNibbles_getElem xs idx hLen
    have hPar : (idx + 2) % 2 = idx % 2 := by omega
    have hDiv : (idx + 2) / 2 = idx / 2 + 1 := by omega
    change (byteNibbles xs)[idx]'hLen = _
    rw [ih]
    by_cases hEven : idx % 2 = 0
    · simp [hEven, hPar, hDiv]
    · simp [hEven, hPar, hDiv]

theorem base2b_4_eq_byteNibbles (xs : List UInt8) :
    base2b xs 4 (2 * xs.length) = byteNibbles xs := by
  apply List.ext_getElem
  · simp [base2b, byteNibbles_length]
  · intro idx h1 h2
    have hIdxLt : idx < 2 * xs.length := by simpa [base2b] using h1
    have hHalf : idx / 2 < xs.length := by omega
    simp only [base2b, List.getElem_map, List.getElem_range]
    rw [msbNibble_eq xs idx hHalf, byteNibbles_getElem xs idx h2]

def fipsSumDigits : List Nat → Nat
  | [] => 0
  | d :: ds => d + fipsSumDigits ds

def fipsWotsChecksum (ell1 : Nat) (msgDigits : List Nat) : Nat :=
  ell1 * 15 - fipsSumDigits msgDigits

/-- NIST FIPS 205 Algorithm 6 WOTS+ ($w = 16$) full digit + 3-nibble shifted-checksum vector. -/
@[expose] def fipsWotsDigits (ell1 : Nat) (msg : List UInt8) : List Nat :=
  let msgDigits := base2b msg 4 ell1
  let csum := fipsWotsChecksum ell1 msgDigits
  let csumBytes := be 2 (csum * 16)
  let csumDigits := base2b csumBytes 4 3
  msgDigits ++ csumDigits

theorem fipsWotsDigits_bounds (ell1 : Nat) (msg : List UInt8) :
    (fipsWotsDigits ell1 msg).length = ell1 + 3 ∧
    ∀ d ∈ fipsWotsDigits ell1 msg, d < 16 := by
  unfold fipsWotsDigits
  obtain ⟨hL1, hB1⟩ := base2b_bounds msg 4 ell1
  obtain ⟨hL2, hB2⟩ := base2b_bounds (be 2 (fipsWotsChecksum ell1 (base2b msg 4 ell1) * 16)) 4 3
  refine ⟨by simp [hL1, hL2], ?_⟩
  intro d hd
  rw [List.mem_append] at hd
  have h16 : (2 : Nat) ^ 4 = 16 := rfl
  rcases hd with hd1 | hd2
  · exact h16 ▸ hB1 d hd1
  · exact h16 ▸ hB2 d hd2

private theorem sumDigits_le_of_pointwise : ∀ {xs ys : List Nat},
    xs.length = ys.length →
    (∀ i (hx : i < xs.length) (hy : i < ys.length), xs[i]'hx ≤ ys[i]'hy) →
    fipsSumDigits xs ≤ fipsSumDigits ys
  | [], [], _, _ => Nat.le_refl 0
  | x :: xs, y :: ys, hLen, hLe => by
    simp only [List.length_cons, Nat.succ.injEq] at hLen
    simp only [fipsSumDigits]
    have h0 : x ≤ y := hLe 0 (by simp) (by simp)
    have hRest := sumDigits_le_of_pointwise hLen
      (fun i hx hy => hLe (i + 1) (Nat.succ_lt_succ hx) (Nat.succ_lt_succ hy))
    omega

private theorem sum_le_and_strict_of_pointwise : ∀ {xs ys : List Nat},
    xs.length = ys.length →
    xs ≠ ys →
    (∀ i (hx : i < xs.length) (hy : i < ys.length), xs[i]'hx ≤ ys[i]'hy) →
    fipsSumDigits xs < fipsSumDigits ys
  | [], [], _, hNe, _ => False.elim (hNe rfl)
  | x :: xs, y :: ys, hLen, hNe, hLe => by
    simp only [List.length_cons, Nat.succ.injEq] at hLen
    simp only [fipsSumDigits]
    have h0 : x ≤ y := hLe 0 (by simp) (by simp)
    have hTailLe : ∀ i (hx : i < xs.length) (hy : i < ys.length), xs[i]'hx ≤ ys[i]'hy :=
      fun i hx hy => hLe (i + 1) (Nat.succ_lt_succ hx) (Nat.succ_lt_succ hy)
    by_cases hxy : x = y
    · subst hxy
      have hTailNe : xs ≠ ys := fun h => hNe (congrArg (x :: ·) h)
      have ih := sum_le_and_strict_of_pointwise hLen hTailNe hTailLe
      omega
    · have hStrict0 : x < y := Nat.lt_of_le_of_ne h0 hxy
      have hTailSumLe : fipsSumDigits xs ≤ fipsSumDigits ys :=
        sumDigits_le_of_pointwise hLen hTailLe
      omega

private theorem fipsSumDigits_le_15_mul : ∀ (ds : List Nat),
    (∀ d ∈ ds, d < 16) → fipsSumDigits ds ≤ ds.length * 15
  | [], _ => by simp [fipsSumDigits]
  | d :: ds, hB => by
    simp only [fipsSumDigits, List.length_cons]
    have hd : d ≤ 15 := by have := hB d (.head _); omega
    have hRest := fipsSumDigits_le_15_mul ds (fun x hx => hB x (.tail _ hx))
    rw [Nat.succ_mul]
    omega

private theorem csum_base2b_reconstruct {c : Nat} (hc : c < 4096) :
    let ds := base2b (be 2 (c * 16)) 4 3
    ds.length = 3 ∧
    256 * (ds.getD 0 0) + 16 * (ds.getD 1 0) + ds.getD 2 0 = c := by
  have hFour : base2b (be 2 (c * 16)) 4 4 = byteNibbles (be 2 (c * 16)) := by
    have hLen2 : 2 * (be 2 (c * 16)).length = 4 := by simp [length_be]
    simpa [hLen2] using base2b_4_eq_byteNibbles (be 2 (c * 16))
  have hTake3 : base2b (be 2 (c * 16)) 4 3 = (base2b (be 2 (c * 16)) 4 4).take 3 := rfl
  have hBe2 : be 2 (c * 16) = [UInt8.ofNat (c * 16 / 256 % 256), UInt8.ofNat (c * 16 % 256)] := rfl
  refine ⟨(base2b_bounds (be 2 (c * 16)) 4 3).1, ?_⟩
  rw [hTake3, hFour, hBe2]
  simp only [byteNibbles, UInt8.toNat_ofNat', List.take, List.getD_cons_zero, List.getD_cons_succ]
  have h8 : (2 : Nat) ^ 8 = 256 := rfl
  rw [h8]
  omega

/-- Constructive backward-step index witness (`ys[idx] < xs[idx]`). -/
structure BackwardIdxWitness (xs ys : List Nat) where
  idx : Nat
  h1  : idx < xs.length
  h2  : idx < ys.length
  hLt : ys[idx]'h2 < xs[idx]'h1

private def decideBackwardOrAllLe :
    (xs ys : List Nat) → xs.length = ys.length →
      PSum (BackwardIdxWitness xs ys)
           (PLift (∀ (idx : Nat) (h1 : idx < xs.length) (h2 : idx < ys.length), xs[idx]'h1 ≤ ys[idx]'h2))
  | [], [], _ => .inr ⟨fun _ h1 _ => nomatch h1⟩
  | x :: xs, y :: ys, hLen =>
    if h0 : y < x then
      .inl ⟨0, Nat.zero_lt_succ _, Nat.zero_lt_succ _, h0⟩
    else
      match decideBackwardOrAllLe xs ys (Nat.succ.inj hLen) with
      | .inl ⟨idx, h1, h2, hLt⟩ =>
        .inl ⟨idx + 1, Nat.succ_lt_succ h1, Nat.succ_lt_succ h2, hLt⟩
      | .inr ⟨hAll⟩ =>
        .inr ⟨fun idx h1 h2 =>
          match idx with
          | 0 => Nat.le_of_not_lt h0
          | k + 1 => hAll k (Nat.lt_of_succ_lt_succ h1) (Nat.lt_of_succ_lt_succ h2)⟩

private theorem getD_append_right_nat : ∀ (xs ys : List Nat) (j : Nat),
    (xs ++ ys).getD (xs.length + j) 0 = ys.getD j 0
  | [], ys, j => by simp
  | _ :: xs, ys, j => by
    simp only [List.cons_append, List.length_cons, Nat.succ_add, List.getD_cons_succ]
    exact getD_append_right_nat xs ys j

private theorem not_all_le_fipsWotsDigits
    {n : Nat} {msg₁ msg₂ : List UInt8}
    (hn : n ≤ 128) (hLen₁ : msg₁.length = n) (hLen₂ : msg₂.length = n)
    (hNe : msg₁ ≠ msg₂)
    (hAllLe : ∀ idx (h1 : idx < (fipsWotsDigits (2 * n) msg₁).length)
                    (h2 : idx < (fipsWotsDigits (2 * n) msg₂).length),
                (fipsWotsDigits (2 * n) msg₁)[idx]'h1 ≤ (fipsWotsDigits (2 * n) msg₂)[idx]'h2) :
    False := by
  have hd1Eq : base2b msg₁ 4 (2 * n) = byteNibbles msg₁ := by simpa [hLen₁] using base2b_4_eq_byteNibbles msg₁
  have hd2Eq : base2b msg₂ 4 (2 * n) = byteNibbles msg₂ := by simpa [hLen₂] using base2b_4_eq_byteNibbles msg₂
  have hdNe : base2b msg₁ 4 (2 * n) ≠ base2b msg₂ 4 (2 * n) :=
    fun hEq => hNe (byteNibbles_injective (hd1Eq.symm.trans (hEq.trans hd2Eq)))
  obtain ⟨hdLen1, hdB1⟩ := base2b_bounds msg₁ 4 (2 * n)
  obtain ⟨hdLen2, hdB2⟩ := base2b_bounds msg₂ 4 (2 * n)
  have hMsgPointwise : ∀ i (hx : i < (base2b msg₁ 4 (2 * n)).length)
                          (hy : i < (base2b msg₂ 4 (2 * n)).length),
      (base2b msg₁ 4 (2 * n))[i]'hx ≤ (base2b msg₂ 4 (2 * n))[i]'hy := by
    intro i hx hy
    have hw1 : i < (fipsWotsDigits (2 * n) msg₁).length := by
      unfold fipsWotsDigits; dsimp only; rw [List.length_append]; omega
    have hw2 : i < (fipsWotsDigits (2 * n) msg₂).length := by
      unfold fipsWotsDigits; dsimp only; rw [List.length_append]; omega
    have hLeW := hAllLe i hw1 hw2
    have hEq1 : (fipsWotsDigits (2 * n) msg₁)[i]'hw1 = (base2b msg₁ 4 (2 * n))[i]'hx :=
      List.getElem_append_left hx
    have hEq2 : (fipsWotsDigits (2 * n) msg₂)[i]'hw2 = (base2b msg₂ 4 (2 * n))[i]'hy :=
      List.getElem_append_left hy
    omega
  have hSumStrict : fipsSumDigits (base2b msg₁ 4 (2 * n)) < fipsSumDigits (base2b msg₂ 4 (2 * n)) :=
    sum_le_and_strict_of_pointwise (hdLen1.trans hdLen2.symm) hdNe hMsgPointwise
  have hSum2Max : fipsSumDigits (base2b msg₂ 4 (2 * n)) ≤ (2 * n) * 15 := by
    have := fipsSumDigits_le_15_mul (base2b msg₂ 4 (2 * n)) (by simpa using hdB2)
    rwa [hdLen2] at this
  have hcStrict : fipsWotsChecksum (2 * n) (base2b msg₂ 4 (2 * n)) <
                  fipsWotsChecksum (2 * n) (base2b msg₁ 4 (2 * n)) := by
    unfold fipsWotsChecksum; omega
  have hc1Lt : fipsWotsChecksum (2 * n) (base2b msg₁ 4 (2 * n)) < 4096 := by
    unfold fipsWotsChecksum; omega
  have hc2Lt : fipsWotsChecksum (2 * n) (base2b msg₂ 4 (2 * n)) < 4096 := by omega
  obtain ⟨hcL1, hcRec1⟩ := csum_base2b_reconstruct hc1Lt
  obtain ⟨hcL2, hcRec2⟩ := csum_base2b_reconstruct hc2Lt
  have hCsLe : ∀ j, j < 3 →
      (base2b (be 2 (fipsWotsChecksum (2 * n) (base2b msg₁ 4 (2 * n)) * 16)) 4 3).getD j 0 ≤
      (base2b (be 2 (fipsWotsChecksum (2 * n) (base2b msg₂ 4 (2 * n)) * 16)) 4 3).getD j 0 := by
    intro j hj
    have hw1 : (base2b msg₁ 4 (2 * n)).length + j < (fipsWotsDigits (2 * n) msg₁).length := by
      unfold fipsWotsDigits; dsimp only; rw [List.length_append, hcL1]; omega
    have hw2' : (base2b msg₁ 4 (2 * n)).length + j < (fipsWotsDigits (2 * n) msg₂).length := by
      unfold fipsWotsDigits; dsimp only; rw [List.length_append, hcL2]; omega
    have hLeW := hAllLe ((base2b msg₁ 4 (2 * n)).length + j) hw1 hw2'
    have hW1D : (fipsWotsDigits (2 * n) msg₁)[(base2b msg₁ 4 (2 * n)).length + j]'hw1 =
        (fipsWotsDigits (2 * n) msg₁).getD ((base2b msg₁ 4 (2 * n)).length + j) 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hw1]; rfl
    have hW2D : (fipsWotsDigits (2 * n) msg₂)[(base2b msg₁ 4 (2 * n)).length + j]'hw2' =
        (fipsWotsDigits (2 * n) msg₂).getD ((base2b msg₁ 4 (2 * n)).length + j) 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hw2']; rfl
    have hGet1 : (fipsWotsDigits (2 * n) msg₁).getD ((base2b msg₁ 4 (2 * n)).length + j) 0 =
        (base2b (be 2 (fipsWotsChecksum (2 * n) (base2b msg₁ 4 (2 * n)) * 16)) 4 3).getD j 0 := by
      unfold fipsWotsDigits; dsimp only
      exact getD_append_right_nat _ _ j
    have hLenEqB : (base2b msg₁ 4 (2 * n)).length = (base2b msg₂ 4 (2 * n)).length :=
      hdLen1.trans hdLen2.symm
    have hGet2 : (fipsWotsDigits (2 * n) msg₂).getD ((base2b msg₁ 4 (2 * n)).length + j) 0 =
        (base2b (be 2 (fipsWotsChecksum (2 * n) (base2b msg₂ 4 (2 * n)) * 16)) 4 3).getD j 0 := by
      rw [hLenEqB]
      unfold fipsWotsDigits; dsimp only
      exact getD_append_right_nat _ _ j
    omega
  have h0 := hCsLe 0 (by decide)
  have h1 := hCsLe 1 (by decide)
  have h2 := hCsLe 2 (by decide)
  omega

/-- Constructive (`Type`-valued, `0 Classical.choice`) witness finder for NIST FIPS 205 WOTS+
    incomparability: given `msg₁ ≠ msg₂` of length `n ≤ 128`, returns the exact chain index `idx`
    where `w₂[idx] < w₁[idx]`. -/
def findFipsWotsBackwardIdx
    {n : Nat} (msg₁ msg₂ : List UInt8)
    (hn : n ≤ 128) (hLen₁ : msg₁.length = n) (hLen₂ : msg₂.length = n)
    (hNe : msg₁ ≠ msg₂) :
    BackwardIdxWitness (fipsWotsDigits (2 * n) msg₁) (fipsWotsDigits (2 * n) msg₂) :=
  have hWLen : (fipsWotsDigits (2 * n) msg₁).length = (fipsWotsDigits (2 * n) msg₂).length := by
    rw [(fipsWotsDigits_bounds (2 * n) msg₁).1, (fipsWotsDigits_bounds (2 * n) msg₂).1]
  match decideBackwardOrAllLe (fipsWotsDigits (2 * n) msg₁) (fipsWotsDigits (2 * n) msg₂) hWLen with
  | .inl witness => witness
  | .inr ⟨hAllLe⟩ => False.elim (not_all_le_fipsWotsDigits hn hLen₁ hLen₂ hNe hAllLe)

/-- **NIST FIPS 205 WOTS+ Checksum Incomparability Theorem (`fips205_wots_incomparable_no_chain_forgery`)**:
    For ANY two distinct `n`-byte digests `msg₁ ≠ msg₂` (`n ≤ 128`, e.g. `n = 16` in `128f`/`128s`),
    their `(2n + 3)`-digit WOTS+ vectors `fipsWotsDigits (2 * n) msg₁` and `fipsWotsDigits (2 * n) msg₂`
    are strictly incomparable (`0 Classical.choice`): the forged vector MUST step strictly backward
    (`d₂[idx] < d₁[idx]`) on at least one chain! -/
theorem fips205_wots_incomparable_no_chain_forgery
    {n : Nat} {msg₁ msg₂ : List UInt8}
    (hn : n ≤ 128) (hLen₁ : msg₁.length = n) (hLen₂ : msg₂.length = n)
    (hNe : msg₁ ≠ msg₂) :
    let w₁ := fipsWotsDigits (2 * n) msg₁
    let w₂ := fipsWotsDigits (2 * n) msg₂
    ∃ (idx : Nat) (h1 : idx < w₁.length) (h2 : idx < w₂.length),
      w₂[idx]'h2 < w₁[idx]'h1 := by
  let w := findFipsWotsBackwardIdx msg₁ msg₂ hn hLen₁ hLen₂ hNe
  exact ⟨w.idx, w.h1, w.h2, w.hLt⟩

/-! ## 4. Exact NIST FIPS 205 WOTS+, XMSS, FORS & Hypertree Algorithms -/

/-- NIST FIPS 205 Algorithm 5 `chain(X, i, s, PK.seed, ADRS)`. -/
def fipsChain (n : Nat) (pkSeed : List UInt8) (layer tree kp chainIdx : Nat) :
    Nat → Nat → List UInt8 → List UInt8
  | _, 0, x => x
  | startIdx, steps + 1, x =>
    let adrs := mkFipsAdrs layer tree .wotsHash kp chainIdx startIdx
    fipsChain n pkSeed layer tree kp chainIdx (startIdx + 1) steps (fipsF n pkSeed adrs x)

theorem fipsChain_zero (n : Nat) (pkSeed : List UInt8) (layer tree kp chainIdx startIdx : Nat) (x : List UInt8) :
    fipsChain n pkSeed layer tree kp chainIdx startIdx 0 x = x := by rfl
theorem fipsChain_succ (n : Nat) (pkSeed : List UInt8) (layer tree kp chainIdx startIdx steps : Nat) (x : List UInt8) :
    fipsChain n pkSeed layer tree kp chainIdx startIdx (steps + 1) x =
      let adrs := mkFipsAdrs layer tree .wotsHash kp chainIdx startIdx
      fipsChain n pkSeed layer tree kp chainIdx (startIdx + 1) steps (fipsF n pkSeed adrs x) := by rfl

theorem fipsChain_add (n : Nat) (pkSeed : List UInt8) (layer tree kp chainIdx : Nat) :
    ∀ (a b startIdx : Nat) (x : List UInt8),
      fipsChain n pkSeed layer tree kp chainIdx (startIdx + a) b
        (fipsChain n pkSeed layer tree kp chainIdx startIdx a x) =
      fipsChain n pkSeed layer tree kp chainIdx startIdx (a + b) x
  | 0, b, startIdx, x => by simp [fipsChain]
  | a + 1, b, startIdx, x => by
    rw [Nat.succ_add]
    simp only [fipsChain]
    have hShift : startIdx + (a + 1) = (startIdx + 1) + a := by omega
    rw [hShift, fipsChain_add n pkSeed layer tree kp chainIdx a b (startIdx + 1)]

@[simp] theorem fipsChain_length (n : Nat) (pkSeed : List UInt8) (layer tree kp chainIdx : Nat) :
    ∀ (startIdx steps : Nat) (x : List UInt8),
      x.length = n → (fipsChain n pkSeed layer tree kp chainIdx startIdx steps x).length = n
  | _, 0, _, hx => hx
  | startIdx, steps + 1, x, _ => by
    simp only [fipsChain]
    exact fipsChain_length n pkSeed layer tree kp chainIdx (startIdx + 1) steps _ (fipsF_length _ _ _ _)

/-- Algorithm 6 `wots_pkGen(SK.seed, PK.seed, ADRS)`. -/
def fipsWotsPkGen (p : Fips205Params) (skSeed pkSeed : List UInt8) (layer tree kp : Nat) : List UInt8 :=
  let tmp := (List.range p.ell).map fun i =>
    let sk := fipsPrf p.n pkSeed skSeed (mkFipsAdrs layer tree .wotsPrf kp i 0)
    fipsChain p.n pkSeed layer tree kp i 0 15 sk
  fipsTl p.n pkSeed (mkFipsAdrs layer tree .wotsPk kp 0 0) tmp

/-- Algorithm 7 `wots_sign(M, SK.seed, PK.seed, ADRS)`. -/
def fipsWotsSign (p : Fips205Params) (msg skSeed pkSeed : List UInt8) (layer tree kp : Nat) : List (List UInt8) :=
  let digits := fipsWotsDigits p.ell1 msg
  (List.range p.ell).map fun i =>
    let sk := fipsPrf p.n pkSeed skSeed (mkFipsAdrs layer tree .wotsPrf kp i 0)
    fipsChain p.n pkSeed layer tree kp i 0 (digits.getD i 0) sk

/-- Algorithm 8 `wots_pkFromSig(sig, M, PK.seed, ADRS)`. -/
def fipsWotsPkFromSig (p : Fips205Params) (sig : List (List UInt8)) (msg pkSeed : List UInt8)
    (layer tree kp : Nat) : List UInt8 :=
  let digits := fipsWotsDigits p.ell1 msg
  let tmp := (List.range p.ell).map fun i =>
    let di := digits.getD i 0
    fipsChain p.n pkSeed layer tree kp i di (15 - di) (sig.getD i [])
  fipsTl p.n pkSeed (mkFipsAdrs layer tree .wotsPk kp 0 0) tmp

private theorem list_getD_map_range_fips {α : Type} (n : Nat) (f : Nat → α) (dflt : α) {i : Nat} (hi : i < n) :
    ((List.range n).map f).getD i dflt = f i := by
  have hi' : i < ((List.range n).map f).length := by simpa using hi
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']
  simp

theorem fipsWotsPkFromSig_wotsSign (p : Fips205Params) (msg skSeed pkSeed : List UInt8)
    (layer tree kp : Nat) :
    fipsWotsPkFromSig p (fipsWotsSign p msg skSeed pkSeed layer tree kp) msg pkSeed layer tree kp =
      fipsWotsPkGen p skSeed pkSeed layer tree kp := by
  unfold fipsWotsPkFromSig fipsWotsSign fipsWotsPkGen
  dsimp only
  obtain ⟨hDLen, hDBound⟩ := fipsWotsDigits_bounds p.ell1 msg
  congr 1
  apply List.map_congr_left
  intro i hiMem
  have hiLt : i < p.ell := List.mem_range.mp hiMem
  rw [list_getD_map_range_fips p.ell _ [] hiLt]
  have hiDig : i < (fipsWotsDigits p.ell1 msg).length := by
    have hEqEll : p.ell = p.ell1 + 3 := rfl
    rw [hDLen, ← hEqEll]
    exact hiLt
  have hDiLt : (fipsWotsDigits p.ell1 msg).getD i 0 < 16 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hiDig]
    exact hDBound _ (List.getElem_mem hiDig)
  have hComp := fipsChain_add p.n pkSeed layer tree kp i
    ((fipsWotsDigits p.ell1 msg).getD i 0)
    (15 - (fipsWotsDigits p.ell1 msg).getD i 0) 0
    (fipsPrf p.n pkSeed skSeed (mkFipsAdrs layer tree .wotsPrf kp i 0))
  simp only [Nat.zero_add] at hComp
  have hSum15 : (fipsWotsDigits p.ell1 msg).getD i 0 + (15 - (fipsWotsDigits p.ell1 msg).getD i 0) = 15 := by omega
  rw [hComp, hSum15]

/-- NIST FIPS 205 Algorithm 9 `xmss_node(SK.seed, i, z, PK.seed, ADRS)`:
    Note `kp = 0`, `f5 = z` (`1..h'`), `f6 = nodeIdx`. -/
def fipsXmssNode (p : Fips205Params) (skSeed pkSeed : List UInt8) (layer tree : Nat) :
    Nat → Nat → List UInt8
  | 0, nodeIdx => fipsWotsPkGen p skSeed pkSeed layer tree nodeIdx
  | z + 1, nodeIdx =>
    let lnode := fipsXmssNode p skSeed pkSeed layer tree z (2 * nodeIdx)
    let rnode := fipsXmssNode p skSeed pkSeed layer tree z (2 * nodeIdx + 1)
    fipsH p.n pkSeed (mkFipsAdrs layer tree .tree 0 (z + 1) nodeIdx) lnode rnode

def fipsXmssAuthPath (p : Fips205Params) (skSeed pkSeed : List UInt8) (layer tree : Nat) :
    Nat → Nat → Nat → List (List UInt8)
  | 0, _, _ => []
  | z + 1, nodeIdx, localIdx =>
    let half := 2 ^ z
    if localIdx < half then
      let rnode := fipsXmssNode p skSeed pkSeed layer tree z (2 * nodeIdx + 1)
      fipsXmssAuthPath p skSeed pkSeed layer tree z (2 * nodeIdx) localIdx ++ [rnode]
    else
      let lnode := fipsXmssNode p skSeed pkSeed layer tree z (2 * nodeIdx)
      fipsXmssAuthPath p skSeed pkSeed layer tree z (2 * nodeIdx + 1) (localIdx - half) ++ [lnode]

/-- Bottom-up Merkle auth path walker matching NIST FIPS 205 Algorithm 11 (`AUTH[0]` = height-1 sibling). -/
def fipsWalkBottomUp (n : Nat) (pkSeed : List UInt8) (layer tree kp : Nat) (ty : FipsAdrsType) :
    Nat → Nat → List UInt8 → List (List UInt8) → List UInt8
  | _, _, node, [] => node
  | z, idx, node, authZ :: rest =>
    let parentIdx := idx / 2
    let adrs := mkFipsAdrs layer tree ty kp (z + 1) parentIdx
    let nextNode := if idx % 2 = 0 then fipsH n pkSeed adrs node authZ else fipsH n pkSeed adrs authZ node
    fipsWalkBottomUp n pkSeed layer tree kp ty (z + 1) parentIdx nextNode rest

private theorem fipsWalkBottomUp_append_single (n : Nat) (pkSeed : List UInt8) (layer tree kp : Nat)
    (ty : FipsAdrsType) :
    ∀ (path : List (List UInt8)) (z idx : Nat) (node lastSib : List UInt8),
      fipsWalkBottomUp n pkSeed layer tree kp ty z idx node (path ++ [lastSib]) =
      let mid := fipsWalkBottomUp n pkSeed layer tree kp ty z idx node path
      let topIdx := idx / (2 ^ path.length)
      let adrs := mkFipsAdrs layer tree ty kp (z + path.length + 1) (topIdx / 2)
      if topIdx % 2 = 0 then fipsH n pkSeed adrs mid lastSib else fipsH n pkSeed adrs lastSib mid
  | [], z, idx, node, lastSib => by simp [fipsWalkBottomUp]
  | a :: rest, z, idx, node, lastSib => by
    simp only [List.cons_append, fipsWalkBottomUp, List.length_cons]
    rw [fipsWalkBottomUp_append_single n pkSeed layer tree kp ty rest (z + 1) (idx / 2)]
    have hDiv : (idx / 2) / (2 ^ rest.length) = idx / (2 ^ (rest.length + 1)) := by
      rw [Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm 2 (2 ^ rest.length)]
    have hZ : (z + 1) + rest.length + 1 = z + (rest.length + 1) + 1 := by omega
    rw [hDiv, hZ]

private theorem fipsXmssAuthPath_length (p : Fips205Params) (skSeed pkSeed : List UInt8)
    (layer tree : Nat) :
    ∀ (z nodeIdx localIdx : Nat), (fipsXmssAuthPath p skSeed pkSeed layer tree z nodeIdx localIdx).length = z
  | 0, _, _ => rfl
  | z + 1, nodeIdx, localIdx => by
    simp only [fipsXmssAuthPath]
    split <;> simp [fipsXmssAuthPath_length p skSeed pkSeed layer tree z]

theorem fipsWalkBottomUp_xmssAuthPath (p : Fips205Params) (skSeed pkSeed : List UInt8)
    (layer tree : Nat) :
    ∀ (z nodeIdx localIdx : Nat), localIdx < 2 ^ z →
      fipsWalkBottomUp p.n pkSeed layer tree 0 .tree 0 (nodeIdx * (2 ^ z) + localIdx)
        (fipsWotsPkGen p skSeed pkSeed layer tree (nodeIdx * (2 ^ z) + localIdx))
        (fipsXmssAuthPath p skSeed pkSeed layer tree z nodeIdx localIdx) =
      fipsXmssNode p skSeed pkSeed layer tree z nodeIdx
  | 0, nodeIdx, localIdx, hLt => by
    have h0 : localIdx = 0 := by simp at hLt; exact hLt
    subst h0; simp [fipsXmssAuthPath, fipsWalkBottomUp, fipsXmssNode]
  | z + 1, nodeIdx, localIdx, hLt => by
    simp only [fipsXmssAuthPath]
    have hMul : nodeIdx * (2 ^ (z + 1)) = (2 * nodeIdx) * (2 ^ z) := by
      rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm (nodeIdx * 2 ^ z) 2, Nat.mul_assoc]
    by_cases hHalf : localIdx < 2 ^ z
    · simp only [hHalf, ↓reduceIte]
      rw [fipsWalkBottomUp_append_single]
      have hIdxEq : nodeIdx * (2 ^ (z + 1)) + localIdx = (2 * nodeIdx) * (2 ^ z) + localIdx := by rw [hMul]
      have ih := fipsWalkBottomUp_xmssAuthPath p skSeed pkSeed layer tree z (2 * nodeIdx) localIdx hHalf
      have hPLen := fipsXmssAuthPath_length p skSeed pkSeed layer tree z (2 * nodeIdx) localIdx
      rw [hIdxEq, ih, hPLen]
      have hTopIdx : ((2 * nodeIdx) * (2 ^ z) + localIdx) / (2 ^ z) = 2 * nodeIdx := by
        have hPos : 0 < 2 ^ z := Nat.two_pow_pos z
        rw [Nat.mul_comm (2 * nodeIdx) (2 ^ z), Nat.mul_add_div hPos, Nat.div_eq_of_lt hHalf, Nat.add_zero]
      have hPar : (2 * nodeIdx) % 2 = 0 := by omega
      have hParent : (2 * nodeIdx) / 2 = nodeIdx := by omega
      simp only [hTopIdx, hPar, ↓reduceIte, hParent, Nat.zero_add, fipsXmssNode]
    · simp only [hHalf, ↓reduceIte]
      rw [fipsWalkBottomUp_append_single]
      have hSubLt : localIdx - 2 ^ z < 2 ^ z := by rw [Nat.pow_succ] at hLt; omega
      have hIdxEq : nodeIdx * (2 ^ (z + 1)) + localIdx = (2 * nodeIdx + 1) * (2 ^ z) + (localIdx - 2 ^ z) := by
        rw [hMul, Nat.add_mul, Nat.one_mul, Nat.add_assoc, Nat.add_sub_of_le (Nat.le_of_not_lt hHalf)]
      have ih := fipsWalkBottomUp_xmssAuthPath p skSeed pkSeed layer tree z (2 * nodeIdx + 1) (localIdx - 2 ^ z) hSubLt
      have hPLen := fipsXmssAuthPath_length p skSeed pkSeed layer tree z (2 * nodeIdx + 1) (localIdx - 2 ^ z)
      rw [hIdxEq, ih, hPLen]
      have hTopIdx : ((2 * nodeIdx + 1) * (2 ^ z) + (localIdx - 2 ^ z)) / (2 ^ z) = 2 * nodeIdx + 1 := by
        have hPos : 0 < 2 ^ z := Nat.two_pow_pos z
        rw [Nat.mul_comm (2 * nodeIdx + 1) (2 ^ z), Nat.mul_add_div hPos, Nat.div_eq_of_lt hSubLt, Nat.add_zero]
      have hPar : ¬ ((2 * nodeIdx + 1) % 2 = 0) := by omega
      have hParent : (2 * nodeIdx + 1) / 2 = nodeIdx := by omega
      simp only [hTopIdx, hPar, ↓reduceIte, hParent, Nat.zero_add, fipsXmssNode]

structure FipsXmssSig where
  wotsSig  : List (List UInt8)
  authPath : List (List UInt8)
  deriving DecidableEq, Repr

/-- Algorithm 10 `xmss_sign(M, SK.seed, idx, PK.seed, ADRS)`. -/
def fipsXmssSign (p : Fips205Params) (msg skSeed pkSeed : List UInt8) (layer tree idx : Nat) : FipsXmssSig :=
  { wotsSig  := fipsWotsSign p msg skSeed pkSeed layer tree idx
    authPath := fipsXmssAuthPath p skSeed pkSeed layer tree p.hp 0 idx }

/-- Algorithm 11 `xmss_pkFromSig(idx, SIG_XMSS, M, PK.seed, ADRS)`. -/
def fipsXmssPkFromSig (p : Fips205Params) (idx : Nat) (xsig : FipsXmssSig) (msg pkSeed : List UInt8)
    (layer tree : Nat) : List UInt8 :=
  let node0 := fipsWotsPkFromSig p xsig.wotsSig msg pkSeed layer tree idx
  fipsWalkBottomUp p.n pkSeed layer tree 0 .tree 0 idx node0 xsig.authPath

theorem fipsXmssPkFromSig_xmssSign (p : Fips205Params) (msg skSeed pkSeed : List UInt8)
    (layer tree idx : Nat) (hIdx : idx < 2 ^ p.hp) :
    fipsXmssPkFromSig p idx (fipsXmssSign p msg skSeed pkSeed layer tree idx) msg pkSeed layer tree =
      fipsXmssNode p skSeed pkSeed layer tree p.hp 0 := by
  unfold fipsXmssPkFromSig fipsXmssSign
  dsimp only
  rw [fipsWotsPkFromSig_wotsSign]
  have hWalk := fipsWalkBottomUp_xmssAuthPath p skSeed pkSeed layer tree p.hp 0 idx hIdx
  simpa using hWalk

/-- NIST FIPS 205 Algorithm 15 `fors_node(SK.seed, i, z, PK.seed, ADRS)`:
    Note `kp = idxLeaf` is preserved across all internal FORS nodes (`f5 = z`, `f6 = nodeIdx`)! -/
def fipsForsNode (p : Fips205Params) (skSeed pkSeed : List UInt8) (tree idxLeaf : Nat) :
    Nat → Nat → List UInt8
  | 0, nodeIdx =>
    let sk := fipsPrf p.n pkSeed skSeed (mkFipsAdrs 0 tree .forsPrf idxLeaf 0 nodeIdx)
    fipsF p.n pkSeed (mkFipsAdrs 0 tree .forsTree idxLeaf 0 nodeIdx) sk
  | z + 1, nodeIdx =>
    let lnode := fipsForsNode p skSeed pkSeed tree idxLeaf z (2 * nodeIdx)
    let rnode := fipsForsNode p skSeed pkSeed tree idxLeaf z (2 * nodeIdx + 1)
    fipsH p.n pkSeed (mkFipsAdrs 0 tree .forsTree idxLeaf (z + 1) nodeIdx) lnode rnode

def fipsForsAuthPath (p : Fips205Params) (skSeed pkSeed : List UInt8) (tree idxLeaf : Nat) :
    Nat → Nat → Nat → List (List UInt8)
  | 0, _, _ => []
  | z + 1, nodeIdx, localIdx =>
    let half := 2 ^ z
    if localIdx < half then
      let rnode := fipsForsNode p skSeed pkSeed tree idxLeaf z (2 * nodeIdx + 1)
      fipsForsAuthPath p skSeed pkSeed tree idxLeaf z (2 * nodeIdx) localIdx ++ [rnode]
    else
      let lnode := fipsForsNode p skSeed pkSeed tree idxLeaf z (2 * nodeIdx)
      fipsForsAuthPath p skSeed pkSeed tree idxLeaf z (2 * nodeIdx + 1) (localIdx - half) ++ [lnode]

private theorem fipsForsAuthPath_length (p : Fips205Params) (skSeed pkSeed : List UInt8)
    (tree idxLeaf : Nat) :
    ∀ (z nodeIdx localIdx : Nat), (fipsForsAuthPath p skSeed pkSeed tree idxLeaf z nodeIdx localIdx).length = z
  | 0, _, _ => rfl
  | z + 1, nodeIdx, localIdx => by
    simp only [fipsForsAuthPath]
    split <;> simp [fipsForsAuthPath_length p skSeed pkSeed tree idxLeaf z]

theorem fipsWalkBottomUp_forsAuthPath (p : Fips205Params) (skSeed pkSeed : List UInt8)
    (tree idxLeaf : Nat) :
    ∀ (z nodeIdx localIdx : Nat), localIdx < 2 ^ z →
      fipsWalkBottomUp p.n pkSeed 0 tree idxLeaf .forsTree 0 (nodeIdx * (2 ^ z) + localIdx)
        (fipsForsNode p skSeed pkSeed tree idxLeaf 0 (nodeIdx * (2 ^ z) + localIdx))
        (fipsForsAuthPath p skSeed pkSeed tree idxLeaf z nodeIdx localIdx) =
      fipsForsNode p skSeed pkSeed tree idxLeaf z nodeIdx
  | 0, nodeIdx, localIdx, hLt => by
    have h0 : localIdx = 0 := by simp at hLt; exact hLt
    subst h0; simp [fipsForsAuthPath, fipsWalkBottomUp, fipsForsNode]
  | z + 1, nodeIdx, localIdx, hLt => by
    simp only [fipsForsAuthPath]
    have hMul : nodeIdx * (2 ^ (z + 1)) = (2 * nodeIdx) * (2 ^ z) := by
      rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm (nodeIdx * 2 ^ z) 2, Nat.mul_assoc]
    by_cases hHalf : localIdx < 2 ^ z
    · simp only [hHalf, ↓reduceIte]
      rw [fipsWalkBottomUp_append_single]
      have hIdxEq : nodeIdx * (2 ^ (z + 1)) + localIdx = (2 * nodeIdx) * (2 ^ z) + localIdx := by rw [hMul]
      have ih := fipsWalkBottomUp_forsAuthPath p skSeed pkSeed tree idxLeaf z (2 * nodeIdx) localIdx hHalf
      have hPLen := fipsForsAuthPath_length p skSeed pkSeed tree idxLeaf z (2 * nodeIdx) localIdx
      rw [hIdxEq, ih, hPLen]
      have hTopIdx : ((2 * nodeIdx) * (2 ^ z) + localIdx) / (2 ^ z) = 2 * nodeIdx := by
        have hPos : 0 < 2 ^ z := Nat.two_pow_pos z
        rw [Nat.mul_comm (2 * nodeIdx) (2 ^ z), Nat.mul_add_div hPos, Nat.div_eq_of_lt hHalf, Nat.add_zero]
      have hPar : (2 * nodeIdx) % 2 = 0 := by omega
      have hParent : (2 * nodeIdx) / 2 = nodeIdx := by omega
      simp only [hTopIdx, hPar, ↓reduceIte, hParent, Nat.zero_add, fipsForsNode]
    · simp only [hHalf, ↓reduceIte]
      rw [fipsWalkBottomUp_append_single]
      have hSubLt : localIdx - 2 ^ z < 2 ^ z := by rw [Nat.pow_succ] at hLt; omega
      have hIdxEq : nodeIdx * (2 ^ (z + 1)) + localIdx = (2 * nodeIdx + 1) * (2 ^ z) + (localIdx - 2 ^ z) := by
        rw [hMul, Nat.add_mul, Nat.one_mul, Nat.add_assoc, Nat.add_sub_of_le (Nat.le_of_not_lt hHalf)]
      have ih := fipsWalkBottomUp_forsAuthPath p skSeed pkSeed tree idxLeaf z (2 * nodeIdx + 1) (localIdx - 2 ^ z) hSubLt
      have hPLen := fipsForsAuthPath_length p skSeed pkSeed tree idxLeaf z (2 * nodeIdx + 1) (localIdx - 2 ^ z)
      rw [hIdxEq, ih, hPLen]
      have hTopIdx : ((2 * nodeIdx + 1) * (2 ^ z) + (localIdx - 2 ^ z)) / (2 ^ z) = 2 * nodeIdx + 1 := by
        have hPos : 0 < 2 ^ z := Nat.two_pow_pos z
        rw [Nat.mul_comm (2 * nodeIdx + 1) (2 ^ z), Nat.mul_add_div hPos, Nat.div_eq_of_lt hSubLt, Nat.add_zero]
      have hPar : ¬ ((2 * nodeIdx + 1) % 2 = 0) := by omega
      have hParent : (2 * nodeIdx + 1) / 2 = nodeIdx := by omega
      simp only [hTopIdx, hPar, ↓reduceIte, hParent, Nat.zero_add, fipsForsNode]

structure FipsForsTreeSig where
  skVal    : List UInt8
  authPath : List (List UInt8)
  deriving DecidableEq, Repr

/-- Algorithm 16 `fors_sign(md, SK.seed, PK.seed, ADRS)`. -/
def fipsForsSign (p : Fips205Params) (md skSeed pkSeed : List UInt8) (tree idxLeaf : Nat) : List FipsForsTreeSig :=
  let indices := base2b md p.a p.k
  (List.range p.k).map fun j =>
    let idxJ := indices.getD j 0
    let globalLeaf := j * (2 ^ p.a) + idxJ
    { skVal    := fipsPrf p.n pkSeed skSeed (mkFipsAdrs 0 tree .forsPrf idxLeaf 0 globalLeaf)
      authPath := fipsForsAuthPath p skSeed pkSeed tree idxLeaf p.a j idxJ }

/-- Algorithm 17 `fors_pkFromSig(SIG_FORS, md, PK.seed, ADRS)`. -/
def fipsForsPkFromSig (p : Fips205Params) (fsig : List FipsForsTreeSig) (md pkSeed : List UInt8)
    (tree idxLeaf : Nat) : List UInt8 :=
  let indices := base2b md p.a p.k
  let roots := (List.range p.k).map fun j =>
    let idxJ := indices.getD j 0
    let entry := fsig.getD j ⟨[], []⟩
    let globalLeaf := j * (2 ^ p.a) + idxJ
    let node0 := fipsF p.n pkSeed (mkFipsAdrs 0 tree .forsTree idxLeaf 0 globalLeaf) entry.skVal
    fipsWalkBottomUp p.n pkSeed 0 tree idxLeaf .forsTree 0 globalLeaf node0 entry.authPath
  fipsTl p.n pkSeed (mkFipsAdrs 0 tree .forsRoots idxLeaf 0 0) roots

def fipsForsPkGen (p : Fips205Params) (skSeed pkSeed : List UInt8) (tree idxLeaf : Nat) : List UInt8 :=
  let roots := (List.range p.k).map fun j =>
    fipsForsNode p skSeed pkSeed tree idxLeaf p.a j
  fipsTl p.n pkSeed (mkFipsAdrs 0 tree .forsRoots idxLeaf 0 0) roots

theorem fipsForsPkFromSig_forsSign (p : Fips205Params) (md skSeed pkSeed : List UInt8)
    (tree idxLeaf : Nat) :
    fipsForsPkFromSig p (fipsForsSign p md skSeed pkSeed tree idxLeaf) md pkSeed tree idxLeaf =
      fipsForsPkGen p skSeed pkSeed tree idxLeaf := by
  unfold fipsForsPkFromSig fipsForsSign fipsForsPkGen
  dsimp only
  obtain ⟨hILen, hIBound⟩ := base2b_bounds md p.a p.k
  congr 1
  apply List.map_congr_left
  intro j hjMem
  have hjLt : j < p.k := List.mem_range.mp hjMem
  have hGet : ((List.range p.k).map fun j' =>
      let idxJ := (base2b md p.a p.k).getD j' 0
      let globalLeaf := j' * 2 ^ p.a + idxJ
      ({ skVal := fipsPrf p.n pkSeed skSeed (mkFipsAdrs 0 tree .forsPrf idxLeaf 0 globalLeaf)
         authPath := fipsForsAuthPath p skSeed pkSeed tree idxLeaf p.a j' idxJ } : FipsForsTreeSig)).getD j ⟨[], []⟩ =
      { skVal := fipsPrf p.n pkSeed skSeed (mkFipsAdrs 0 tree .forsPrf idxLeaf 0 (j * 2 ^ p.a + (base2b md p.a p.k).getD j 0))
        authPath := fipsForsAuthPath p skSeed pkSeed tree idxLeaf p.a j ((base2b md p.a p.k).getD j 0) } :=
    list_getD_map_range_fips p.k _ ({ skVal := [], authPath := [] } : FipsForsTreeSig) hjLt
  rw [hGet]
  dsimp only
  have hjIdx : j < (base2b md p.a p.k).length := by omega
  have hIdxJLt : (base2b md p.a p.k).getD j 0 < 2 ^ p.a := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjIdx]
    exact hIBound _ (List.getElem_mem hjIdx)
  exact fipsWalkBottomUp_forsAuthPath p skSeed pkSeed tree idxLeaf p.a j ((base2b md p.a p.k).getD j 0) hIdxJLt

/-! ## 5. Exact Algorithm 12/13 Hypertree & Algorithm 18/19/20 `SLH-DSA` Sign/Verify -/

structure SlhSecretKey where
  skSeed : List UInt8
  skPrf  : List UInt8
  pkSeed : List UInt8
  pkRoot : List UInt8
  deriving DecidableEq, Repr

structure SlhPublicKey where
  pkSeed : List UInt8
  pkRoot : List UInt8
  deriving DecidableEq, Repr

structure SlhSignature where
  rRand   : List UInt8
  forsSig : List FipsForsTreeSig
  htSig   : List FipsXmssSig
  deriving DecidableEq, Repr

/-- Algorithm 18 `slh_keygen_internal(SK.seed, SK.prf, PK.seed)`. -/
@[expose] def slhKeygenInternal (p : Fips205Params) (skSeed skPrf pkSeed : List UInt8) : SlhSecretKey × SlhPublicKey :=
  let pkRoot := fipsXmssNode p skSeed pkSeed (p.d - 1) 0 p.hp 0
  ({ skSeed := skSeed, skPrf := skPrf, pkSeed := pkSeed, pkRoot := pkRoot },
   { pkSeed := pkSeed, pkRoot := pkRoot })

def fipsHtSignAux (p : Fips205Params) (skSeed pkSeed : List UInt8) :
    Nat → Nat → Nat → List UInt8 → Nat → List FipsXmssSig
  | _, _, _, _, 0 => []
  | layer, idxTree, idxLeaf, curMsg, rem + 1 =>
    let sigTmp := fipsXmssSign p curMsg skSeed pkSeed layer idxTree idxLeaf
    let root := fipsXmssNode p skSeed pkSeed layer idxTree p.hp 0
    let nextLeaf := idxTree % (2 ^ p.hp)
    let nextTree := idxTree / (2 ^ p.hp)
    sigTmp :: fipsHtSignAux p skSeed pkSeed (layer + 1) nextTree nextLeaf root rem

def fipsHtVerifyAux (p : Fips205Params) (pkSeed : List UInt8) :
    Nat → Nat → Nat → List UInt8 → List FipsXmssSig → List UInt8
  | _, _, _, curNode, [] => curNode
  | layer, idxTree, idxLeaf, curNode, xsig :: rest =>
    let nextNode := fipsXmssPkFromSig p idxLeaf xsig curNode pkSeed layer idxTree
    let nextLeaf := idxTree % (2 ^ p.hp)
    let nextTree := idxTree / (2 ^ p.hp)
    fipsHtVerifyAux p pkSeed (layer + 1) nextTree nextLeaf nextNode rest

private theorem fipsHtVerifyAux_htSignAux (p : Fips205Params) (skSeed pkSeed : List UInt8) :
    ∀ (rem layer idxTree idxLeaf : Nat) (curMsg : List UInt8),
      0 < rem →
      idxLeaf < 2 ^ p.hp →
      idxTree < 2 ^ ((rem - 1) * p.hp) →
      fipsHtVerifyAux p pkSeed layer idxTree idxLeaf curMsg
        (fipsHtSignAux p skSeed pkSeed layer idxTree idxLeaf curMsg rem) =
      fipsXmssNode p skSeed pkSeed (layer + rem - 1) 0 p.hp 0
  | 0, _, _, _, _, hPos, _, _ => by omega
  | 1, layer, idxTree, idxLeaf, curMsg, _, hLeafLt, hTreeLt => by
    have hTree0 : idxTree = 0 := by simp at hTreeLt; exact hTreeLt
    subst hTree0
    simp only [fipsHtSignAux, fipsHtVerifyAux, fipsXmssPkFromSig_xmssSign p curMsg skSeed pkSeed layer 0 idxLeaf hLeafLt,
               Nat.add_sub_cancel]
  | rem + 2, layer, idxTree, idxLeaf, curMsg, _, hLeafLt, hTreeLt => by
    have hStep :
        fipsHtVerifyAux p pkSeed layer idxTree idxLeaf curMsg
          (fipsHtSignAux p skSeed pkSeed layer idxTree idxLeaf curMsg (rem + 2)) =
        fipsHtVerifyAux p pkSeed (layer + 1) (idxTree / (2 ^ p.hp)) (idxTree % (2 ^ p.hp))
          (fipsXmssNode p skSeed pkSeed layer idxTree p.hp 0)
          (fipsHtSignAux p skSeed pkSeed (layer + 1) (idxTree / (2 ^ p.hp)) (idxTree % (2 ^ p.hp))
            (fipsXmssNode p skSeed pkSeed layer idxTree p.hp 0) (rem + 1)) := by
      conv => lhs; unfold fipsHtSignAux; unfold fipsHtVerifyAux
      dsimp only
      rw [fipsXmssPkFromSig_xmssSign p curMsg skSeed pkSeed layer idxTree idxLeaf hLeafLt]
    rw [hStep]
    have hSubPos : 0 < 2 ^ p.hp := Nat.two_pow_pos p.hp
    have hNextLeafLt : idxTree % (2 ^ p.hp) < 2 ^ p.hp := Nat.mod_lt _ hSubPos
    have hNextTreeLt : idxTree / (2 ^ p.hp) < 2 ^ (rem * p.hp) := by
      have hPow : 2 ^ ((rem + 1) * p.hp) = 2 ^ (rem * p.hp) * 2 ^ p.hp := by
        rw [Nat.succ_mul, Nat.pow_add]
      have hTreeLt' : idxTree < 2 ^ ((rem + 1) * p.hp) := by simpa using hTreeLt
      exact (Nat.div_lt_iff_lt_mul hSubPos).mpr (hPow ▸ hTreeLt')
    have ih := fipsHtVerifyAux_htSignAux p skSeed pkSeed (rem + 1) (layer + 1)
      (idxTree / (2 ^ p.hp)) (idxTree % (2 ^ p.hp))
      (fipsXmssNode p skSeed pkSeed layer idxTree p.hp 0) (by omega) hNextLeafLt (by simpa using hNextTreeLt)
    rw [ih]
    have hTopEq : layer + 1 + (rem + 1) - 1 = layer + (rem + 2) - 1 := by omega
    rw [hTopEq]

/-- Split `H_msg` digest into `(md, idx_tree, idx_leaf)` per FIPS 205 Algorithm 19 Steps 5–10. -/
def fipsSplitDigest (p : Fips205Params) (digest : List UInt8) : List UInt8 × Nat × Nat :=
  let md := digest.take p.mdBytes
  let rawTree := (digest.drop p.mdBytes).take p.treeBytes
  let rawLeaf := (digest.drop (p.mdBytes + p.treeBytes)).take p.leafBytes
  let idxTree := (ofBE rawTree) % (2 ^ (p.h - p.hp))
  let idxLeaf := (ofBE rawLeaf) % (2 ^ p.hp)
  (md, idxTree, idxLeaf)

/-- Algorithm 19 `slh_sign_internal(M', SK, addrnd)`. -/
@[expose] def slhSignInternal (p : Fips205Params) (msgPrime : List UInt8) (sk : SlhSecretKey)
    (optRand : List UInt8) : SlhSignature :=
  let rRand := fipsPrfMsg p.n sk.skPrf optRand msgPrime
  let digest := fipsHMsg p.m rRand sk.pkSeed sk.pkRoot msgPrime
  let (md, idxTree, idxLeaf) := fipsSplitDigest p digest
  let forsSig := fipsForsSign p md sk.skSeed sk.pkSeed idxTree idxLeaf
  let pkFors := fipsForsPkFromSig p forsSig md sk.pkSeed idxTree idxLeaf
  let htSig := fipsHtSignAux p sk.skSeed sk.pkSeed 0 idxTree idxLeaf pkFors p.d
  { rRand := rRand, forsSig := forsSig, htSig := htSig }

/-- Exact nested vector sizes at the structured Algorithm 20 boundary. -/
def fipsXmssSigShape (p : Fips205Params) (sig : FipsXmssSig) : Bool :=
  decide (sig.wotsSig.length = p.ell) &&
  sig.wotsSig.all (fun x => decide (x.length = p.n)) &&
  decide (sig.authPath.length = p.hp) &&
  sig.authPath.all (fun x => decide (x.length = p.n))

def fipsForsSigShape (p : Fips205Params) (sig : FipsForsTreeSig) : Bool :=
  decide (sig.skVal.length = p.n) &&
  decide (sig.authPath.length = p.a) &&
  sig.authPath.all (fun x => decide (x.length = p.n))

private theorem fipsXmssNode_width (p : Fips205Params) (skSeed pkSeed : List UInt8)
    (layer tree : Nat) (z ni : Nat) :
    (fipsXmssNode p skSeed pkSeed layer tree z ni).length = p.n := by
  cases z <;> simp [fipsXmssNode, fipsWotsPkGen]

private theorem fipsXmssAuthPath_width (p : Fips205Params) (skSeed pkSeed : List UInt8)
    (layer tree : Nat) (z ni li : Nat) :
    (fipsXmssAuthPath p skSeed pkSeed layer tree z ni li).all
      (fun x => decide (x.length = p.n)) = true := by
  induction z generalizing ni li with
  | zero => rfl
  | succ z ih =>
    simp only [fipsXmssAuthPath]
    split <;> simp [List.all_append, ih, fipsXmssNode_width]

private theorem fipsForsNode_width (p : Fips205Params) (skSeed pkSeed : List UInt8)
    (tree idxLeaf : Nat) (z ni : Nat) :
    (fipsForsNode p skSeed pkSeed tree idxLeaf z ni).length = p.n := by
  cases z <;> simp [fipsForsNode]

private theorem fipsForsAuthPath_width (p : Fips205Params) (skSeed pkSeed : List UInt8)
    (tree idxLeaf : Nat) (z ni li : Nat) :
    (fipsForsAuthPath p skSeed pkSeed tree idxLeaf z ni li).all
      (fun x => decide (x.length = p.n)) = true := by
  induction z generalizing ni li with
  | zero => rfl
  | succ z ih =>
    simp only [fipsForsAuthPath]
    split <;> simp [List.all_append, ih, fipsForsNode_width]

private theorem fipsXmssSign_shape (p : Fips205Params) (msg skSeed pkSeed : List UInt8)
    (layer tree idx : Nat) :
    fipsXmssSigShape p (fipsXmssSign p msg skSeed pkSeed layer tree idx) = true := by
  simp [fipsXmssSigShape, fipsXmssSign, fipsWotsSign, fipsChain_length,
    fipsXmssAuthPath_length, fipsXmssAuthPath_width]

private theorem fipsForsSign_shape (p : Fips205Params) (md skSeed pkSeed : List UInt8)
    (tree idxLeaf : Nat) :
    (fipsForsSign p md skSeed pkSeed tree idxLeaf).all (fipsForsSigShape p) = true := by
  simp [fipsForsSign, fipsForsSigShape, fipsForsAuthPath_length, fipsForsAuthPath_width]

private theorem fipsHtSignAux_shape (p : Fips205Params) (skSeed pkSeed : List UInt8)
    (rem layer it il : Nat) (msg : List UInt8) :
    (fipsHtSignAux p skSeed pkSeed layer it il msg rem).all (fipsXmssSigShape p) = true := by
  induction rem generalizing layer it il msg with
  | zero => rfl
  | succ rem ih => simp [fipsHtSignAux, fipsXmssSign_shape, ih]

/-- Algorithm 20 `slh_verify_internal(M', SIG, PK)`. -/
@[expose] def slhVerifyInternal (p : Fips205Params) (msgPrime : List UInt8) (sig : SlhSignature)
    (pk : SlhPublicKey) : Bool :=
  if sig.rRand.length ≠ p.n || sig.forsSig.length ≠ p.k || sig.htSig.length ≠ p.d ||
      !(sig.forsSig.all (fipsForsSigShape p)) || !(sig.htSig.all (fipsXmssSigShape p)) then false
  else
    let digest := fipsHMsg p.m sig.rRand pk.pkSeed pk.pkRoot msgPrime
    let (md, idxTree, idxLeaf) := fipsSplitDigest p digest
    let pkFors := fipsForsPkFromSig p sig.forsSig md pk.pkSeed idxTree idxLeaf
    let computedRoot := fipsHtVerifyAux p pk.pkSeed 0 idxTree idxLeaf pkFors sig.htSig
    decide (computedRoot = pk.pkRoot)

/-- Acceptance requires every nested FORS and XMSS signature to have its exact shape. -/
theorem slhVerifyInternal_shapes (p : Fips205Params) (msg : List UInt8)
    (sig : SlhSignature) (pk : SlhPublicKey)
    (h : slhVerifyInternal p msg sig pk = true) :
    sig.rRand.length = p.n ∧ sig.forsSig.length = p.k ∧ sig.htSig.length = p.d ∧
    sig.forsSig.all (fipsForsSigShape p) = true ∧
    sig.htSig.all (fipsXmssSigShape p) = true := by
  unfold slhVerifyInternal at h
  split at h
  · contradiction
  · rename_i hs
    simp only [Bool.or_eq_true, Bool.not_eq_true, decide_eq_true_eq, not_or] at hs
    exact ⟨Decidable.of_not_not hs.1.1.1.1, Decidable.of_not_not hs.1.1.1.2,
      Decidable.of_not_not hs.1.1.2, (by simpa only [Bool.not_eq_false'] using hs.1.2),
      (by simpa only [Bool.not_eq_false'] using hs.2)⟩

/-- Adding even one byte as an extra WOTS element is rejected before hashing. -/
theorem tooth_slh_trailing_wots_rejected (p : Fips205Params) (msg : List UInt8)
    (sig : SlhSignature) (pk : SlhPublicKey) (x : FipsXmssSig) (rest : List FipsXmssSig)
    (hLen : x.wotsSig.length = p.ell) :
    slhVerifyInternal p msg
      { sig with htSig := { x with wotsSig := x.wotsSig ++ [[0]] } :: rest } pk = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  have hs := (slhVerifyInternal_shapes p msg _ pk h).2.2.2.2
  simp only [List.all_cons, Bool.and_eq_true] at hs
  have hc := hs.1
  simp only [fipsXmssSigShape, Bool.and_eq_true, decide_eq_true_eq] at hc
  have bad := hc.1.1.1
  simp only [List.length_append, List.length_cons, List.length_nil, hLen] at bad
  omega

private theorem fipsHtSignAux_length (p : Fips205Params) (skSeed pkSeed : List UInt8) :
    ∀ (rem layer idxTree idxLeaf : Nat) (curMsg : List UInt8),
      (fipsHtSignAux p skSeed pkSeed layer idxTree idxLeaf curMsg rem).length = rem
  | 0, _, _, _, _ => rfl
  | rem + 1, layer, idxTree, idxLeaf, curMsg => by
    simp [fipsHtSignAux, fipsHtSignAux_length p skSeed pkSeed rem]

/-- **Unconditional NIST FIPS 205 Completeness (`slhVerifyInternal_slhSignInternal`)**:
    For every well-formed FIPS 205 parameter set (`SLH-DSA-SHAKE-128f`, `SLH-DSA-SHAKE-128s`, etc.),
    `slhVerifyInternal` accepts every signature produced by `slhSignInternal` under `slhKeygenInternal`. -/
theorem slhVerifyInternal_slhSignInternal (p : Fips205Params) (hWf : p.wellFormed = true)
    (skSeed skPrf pkSeed msgPrime optRand : List UInt8) :
    let (sk, pk) := slhKeygenInternal p skSeed skPrf pkSeed
    slhVerifyInternal p msgPrime (slhSignInternal p msgPrime sk optRand) pk = true := by
  simp only [Fips205Params.wellFormed, Bool.and_eq_true, decide_eq_true_eq] at hWf
  rcases hWf with ⟨⟨⟨⟨⟨⟨hnPos, _⟩, hdPos⟩, hHdEq⟩, _⟩, _⟩, _⟩
  dsimp only [slhKeygenInternal, slhSignInternal, slhVerifyInternal]
  have hRLen : (fipsPrfMsg p.n skPrf optRand msgPrime).length = p.n := shake256Xof_length p.n _
  let digest := fipsHMsg p.m (fipsPrfMsg p.n skPrf optRand msgPrime) pkSeed
                  (fipsXmssNode p skSeed pkSeed (p.d - 1) 0 p.hp 0) msgPrime
  let split := fipsSplitDigest p digest
  have hFLen : (fipsForsSign p split.1 skSeed pkSeed split.2.1 split.2.2).length = p.k := by
    simp [fipsForsSign]
  have hHtLen : (fipsHtSignAux p skSeed pkSeed 0 split.2.1 split.2.2
      (fipsForsPkFromSig p (fipsForsSign p split.1 skSeed pkSeed split.2.1 split.2.2) split.1 pkSeed split.2.1 split.2.2) p.d).length = p.d :=
    fipsHtSignAux_length p skSeed pkSeed p.d 0 _ _ _
  simp only [fipsForsSign_shape, fipsHtSignAux_shape, Bool.not_true, Bool.or_false]
  change (if (fipsPrfMsg p.n skPrf optRand msgPrime).length ≠ p.n ||
             (fipsForsSign p split.1 skSeed pkSeed split.2.1 split.2.2).length ≠ p.k ||
             (fipsHtSignAux p skSeed pkSeed 0 split.2.1 split.2.2
               (fipsForsPkFromSig p (fipsForsSign p split.1 skSeed pkSeed split.2.1 split.2.2) split.1 pkSeed split.2.1 split.2.2) p.d).length ≠ p.d
          then false else _) = true
  simp only [hRLen, hFLen, hHtLen, ne_eq, not_true_eq_false]
  have hLeafLt : split.2.2 < 2 ^ p.hp := Nat.mod_lt _ (Nat.two_pow_pos p.hp)
  have hTreeExp : p.h - p.hp = (p.d - 1) * p.hp := by
    have hd1 : p.d = (p.d - 1) + 1 := by omega
    have hMul : p.d * p.hp = (p.d - 1) * p.hp + p.hp := by
      conv => lhs; rw [hd1]
      rw [Nat.succ_mul]
    omega
  have hTreeLt : split.2.1 < 2 ^ ((p.d - 1) * p.hp) := by
    rw [← hTreeExp]
    exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have hHtSound := fipsHtVerifyAux_htSignAux p skSeed pkSeed p.d 0 split.2.1 split.2.2
    (fipsForsPkFromSig p (fipsForsSign p split.1 skSeed pkSeed split.2.1 split.2.2) split.1 pkSeed split.2.1 split.2.2)
    hdPos hLeafLt hTreeLt
  simp only [Nat.zero_add] at hHtSound
  change decide (fipsHtVerifyAux p pkSeed 0 split.2.1 split.2.2
    (fipsForsPkFromSig p (fipsForsSign p split.1 skSeed pkSeed split.2.1 split.2.2) split.1 pkSeed split.2.1 split.2.2)
    (fipsHtSignAux p skSeed pkSeed 0 split.2.1 split.2.2
      (fipsForsPkFromSig p (fipsForsSign p split.1 skSeed pkSeed split.2.1 split.2.2) split.1 pkSeed split.2.1 split.2.2) p.d) =
    fipsXmssNode p skSeed pkSeed (p.d - 1) 0 p.hp 0) = true
  rw [hHtSound]
  simp

/-- §9.2 Pure FIPS 205 domain-separated message `M' = 0x00 || |ctx| || ctx || M` (`|ctx| ≤ 255`). -/
def encodePureMsgPrime (ctx msg : List UInt8) : Option (List UInt8) :=
  if 255 < ctx.length then none
  else some ((0x00 : UInt8) :: UInt8.ofNat ctx.length :: (ctx ++ msg))

/-- Pure FIPS 205 Algorithm 22 `slh_sign(M, ctx, SK, addrnd)` (`0x00 || |ctx| || ctx || M`). -/
def slhSignPure (p : Fips205Params) (msg ctx : List UInt8) (sk : SlhSecretKey)
    (optRand : List UInt8) : Option SlhSignature :=
  match encodePureMsgPrime ctx msg with
  | none => none
  | some msgPrime => some (slhSignInternal p msgPrime sk optRand)

/-- Pure FIPS 205 Algorithm 24 `slh_verify(M, SIG, ctx, PK)`. -/
def slhVerifyPure (p : Fips205Params) (msg : List UInt8) (sig : SlhSignature)
    (ctx : List UInt8) (pk : SlhPublicKey) : Bool :=
  match encodePureMsgPrime ctx msg with
  | none => false
  | some msgPrime => slhVerifyInternal p msgPrime sig pk

/-- NIST FIPS 205 §9.3 / §10.2 approved Pre-Hash identifiers for `HashSLH-DSA`. -/
inductive FipsPreHashAlg where
  | sha256       -- DER OID `2.16.840.1.101.3.4.2.1` (32B digest, Category 1 = 16B)
  | sha3_256
  | sha3_384
  | sha3_512
  | sha512       -- DER OID `2.16.840.1.101.3.4.2.3` (64B digest, Category 5 = 32B)
  | shake128_256 -- DER OID `2.16.840.1.101.3.4.2.11` (32B XOF, Category 1 = 16B)
  | shake256_512 -- DER OID `2.16.840.1.101.3.4.2.12` (64B XOF, Category 5 = 32B)
  deriving DecidableEq, Repr, Inhabited

def FipsPreHashAlg.oidBytes : FipsPreHashAlg → List UInt8
  | .sha256       => [0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x01]
  | .sha3_256     => [0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x08]
  | .sha3_384     => [0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x09]
  | .sha3_512     => [0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x0A]
  | .sha512       => [0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x03]
  | .shake128_256 => [0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x0B]
  | .shake256_512 => [0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x0C]

def FipsPreHashAlg.digestBytes : FipsPreHashAlg → Nat
  | .sha256       => 32
  | .sha3_256     => 32
  | .sha3_384     => 48
  | .sha3_512     => 64
  | .sha512       => 64
  | .shake128_256 => 32
  | .shake256_512 => 64

def FipsPreHashAlg.securityBytes : FipsPreHashAlg → Nat
  | .sha256       => 16
  | .sha3_256     => 16
  | .sha3_384     => 24
  | .sha3_512     => 32
  | .sha512       => 32
  | .shake128_256 => 16
  | .shake256_512 => 32

theorem FipsPreHashAlg.oidBytes_length (alg : FipsPreHashAlg) : alg.oidBytes.length = 11 := by
  cases alg <;> rfl

theorem FipsPreHashAlg.oidBytes_injective {a b : FipsPreHashAlg}
    (h : a.oidBytes = b.oidBytes) : a = b := by
  cases a <;> cases b <;> simp [FipsPreHashAlg.oidBytes] at h <;> rfl

/-- NIST FIPS 205 §10.2 security-category gate: Category 3/5 (`n ∈ {24, 32}`) MUST reject
    Category-1 (`128`-bit collision) pre-hash functions (`sha256`, `shake128_256`). -/
def preHashCompatible (p : Fips205Params) (alg : FipsPreHashAlg) : Bool :=
  decide (p.n ≤ alg.securityBytes)

/-- §9.3 `HashSLH-DSA` domain-separated message `M' = 0x01 || |ctx| || ctx || OID || PH(M)`. -/
def encodePreHashMsgPrime (p : Fips205Params) (alg : FipsPreHashAlg)
    (ctx phDigest : List UInt8) : Option (List UInt8) :=
  if 255 < ctx.length || !preHashCompatible p alg || phDigest.length ≠ alg.digestBytes then none
  else some ((0x01 : UInt8) :: UInt8.ofNat ctx.length :: (ctx ++ (alg.oidBytes ++ phDigest)))

def slhSignPreHash (p : Fips205Params) (alg : FipsPreHashAlg) (ctx phDigest : List UInt8)
    (sk : SlhSecretKey) (optRand : List UInt8) : Option SlhSignature :=
  match encodePreHashMsgPrime p alg ctx phDigest with
  | none => none
  | some msgPrime => some (slhSignInternal p msgPrime sk optRand)

def slhVerifyPreHash (p : Fips205Params) (alg : FipsPreHashAlg) (ctx phDigest : List UInt8)
    (sig : SlhSignature) (pk : SlhPublicKey) : Bool :=
  match encodePreHashMsgPrime p alg ctx phDigest with
  | none => false
  | some msgPrime => slhVerifyInternal p msgPrime sig pk

private theorem uint8_ofNat_inj_le255 {a b : Nat} (ha : a ≤ 255) (hb : b ≤ 255)
    (h : UInt8.ofNat a = UInt8.ofNat b) : a = b := by
  have hv := congrArg UInt8.toNat h
  simp only [UInt8.toNat_ofNat'] at hv
  have hm1 : a % 256 = a := Nat.mod_eq_of_lt (by omega)
  have hm2 : b % 256 = b := Nat.mod_eq_of_lt (by omega)
  omega

/-- **Unconditional §9.2 Pure vs §9.3 PreHash Domain Separation (`pure_vs_preHash_disjoint`)**. -/
theorem pure_vs_preHash_disjoint (p₂ : Fips205Params) (alg : FipsPreHashAlg)
    (ctx₁ msg₁ ctx₂ ph₂ mp₁ mp₂ : List UInt8)
    (hPure : encodePureMsgPrime ctx₁ msg₁ = some mp₁)
    (hPre  : encodePreHashMsgPrime p₂ alg ctx₂ ph₂ = some mp₂) :
    mp₁ ≠ mp₂ := by
  unfold encodePureMsgPrime at hPure
  unfold encodePreHashMsgPrime at hPre
  split at hPure
  · cases hPure
  · split at hPre
    · cases hPre
    · injection hPure with hp1
      injection hPre with hp2
      subst hp1 hp2
      intro hEq
      injection hEq with hTag _
      cases hTag

/-- **§9.2 Pure Context + Message Injectivity (`encodePureMsgPrime_injective`)**. -/
theorem encodePureMsgPrime_injective {ctx₁ msg₁ ctx₂ msg₂ mp : List UInt8}
    (h1 : encodePureMsgPrime ctx₁ msg₁ = some mp)
    (h2 : encodePureMsgPrime ctx₂ msg₂ = some mp) :
    ctx₁ = ctx₂ ∧ msg₁ = msg₂ := by
  unfold encodePureMsgPrime at h1 h2
  split at h1
  · cases h1
  · rename_i hle1
    split at h2
    · cases h2
    · rename_i hle2
      injection h1 with e1
      injection h2 with e2
      have hComb : (0x00 : UInt8) :: UInt8.ofNat ctx₁.length :: (ctx₁ ++ msg₁) =
                   (0x00 : UInt8) :: UInt8.ofNat ctx₂.length :: (ctx₂ ++ msg₂) := e1.trans e2.symm
      injection hComb with _ hTail1
      injection hTail1 with hLenByte hRest
      have hLenEq : ctx₁.length = ctx₂.length :=
        uint8_ofNat_inj_le255 (by omega) (by omega) hLenByte
      exact List.append_inj hRest hLenEq

/-- **§9.3 Pre-Hash OID + Context + Digest Injectivity (`encodePreHashMsgPrime_injective`)**. -/
theorem encodePreHashMsgPrime_injective {p : Fips205Params}
    {alg₁ alg₂ : FipsPreHashAlg} {ctx₁ d₁ ctx₂ d₂ mp : List UInt8}
    (h1 : encodePreHashMsgPrime p alg₁ ctx₁ d₁ = some mp)
    (h2 : encodePreHashMsgPrime p alg₂ ctx₂ d₂ = some mp) :
    alg₁ = alg₂ ∧ ctx₁ = ctx₂ ∧ d₁ = d₂ := by
  unfold encodePreHashMsgPrime at h1 h2
  split at h1
  · cases h1
  · rename_i hBad1
    split at h2
    · cases h2
    · rename_i hBad2
      have hc1 : ctx₁.length ≤ 255 :=
        if hgt : 255 < ctx₁.length then False.elim (hBad1 (by simp [hgt])) else Nat.le_of_not_lt hgt
      have hc2 : ctx₂.length ≤ 255 :=
        if hgt : 255 < ctx₂.length then False.elim (hBad2 (by simp [hgt])) else Nat.le_of_not_lt hgt
      injection h1 with e1
      injection h2 with e2
      have hComb := e1.trans e2.symm
      injection hComb with _ hTail1
      injection hTail1 with hLenByte hRest
      have hCtxLen : ctx₁.length = ctx₂.length := uint8_ofNat_inj_le255 hc1 hc2 hLenByte
      obtain ⟨hCtxEq, hOidAndDig⟩ := List.append_inj hRest hCtxLen
      have hOidLen : alg₁.oidBytes.length = alg₂.oidBytes.length := by
        rw [FipsPreHashAlg.oidBytes_length, FipsPreHashAlg.oidBytes_length]
      obtain ⟨hOidEq, hDigEq⟩ := List.append_inj hOidAndDig hOidLen
      exact ⟨FipsPreHashAlg.oidBytes_injective hOidEq, hCtxEq, hDigEq⟩

/-- **Pre-Hash Downgrade Rejection Tooth (`preHash_downgrade_rejected`)**:
    Category 3 (`192f`) and Category 5 (`256s`) strictly reject Category-1 (`sha256`, `shake128_256`) pre-hashes. -/
theorem preHash_downgrade_rejected (ctx d optRand : List UInt8) (sk : SlhSecretKey) :
    slhSignPreHash slhDsaShake192f .sha256 ctx d sk optRand = none ∧
    slhSignPreHash slhDsaShake256s .shake128_256 ctx d sk optRand = none := by
  unfold slhSignPreHash encodePreHashMsgPrime preHashCompatible slhDsaShake192f slhDsaShake256s FipsPreHashAlg.securityBytes
  refine ⟨?_, ?_⟩ <;> simp

theorem slhVerifyPreHash_slhSignPreHash (p : Fips205Params) (hWf : p.wellFormed = true)
    (alg : FipsPreHashAlg) (skSeed skPrf pkSeed ctx phDigest optRand : List UInt8)
    (hCtx : ctx.length ≤ 255) (hCompat : preHashCompatible p alg = true)
    (hDigLen : phDigest.length = alg.digestBytes) :
    let (sk, pk) := slhKeygenInternal p skSeed skPrf pkSeed
    ∃ sig, slhSignPreHash p alg ctx phDigest sk optRand = some sig ∧
           slhVerifyPreHash p alg ctx phDigest sig pk = true := by
  dsimp only
  have hNotGt : ¬ (255 < ctx.length) := by omega
  unfold slhSignPreHash slhVerifyPreHash encodePreHashMsgPrime
  simp only [hNotGt, decide_false, hCompat, Bool.not_true, hDigLen, ne_eq, not_true_eq_false,
             Bool.false_or]
  exact ⟨_, rfl, slhVerifyInternal_slhSignInternal p hWf skSeed skPrf pkSeed _ optRand⟩

/-! ## 6. Exact `17,088`B / `7,856`B FIPS 205 Signature Serialization & Threshold Bit-Identity -/

/-- Exact NIST FIPS 205 Figure 15 flat byte serialization of `SlhSignature`:
    `R || SIG_FORS || SIG_HT` (`17,088` bytes for `128f`, `7,856` bytes for `128s`). -/
@[expose] def encodeSlhSig (sig : SlhSignature) : List UInt8 :=
  sig.rRand ++
  (sig.forsSig.map fun f => f.skVal ++ f.authPath.flatten).flatten ++
  (sig.htSig.map fun x => x.wotsSig.flatten ++ x.authPath.flatten).flatten

private theorem flatten_map_fixed_len {α : Type} (xs : List α) (f : α → List UInt8) (c : Nat)
    (hEach : ∀ x ∈ xs, (f x).length = c) :
    (xs.map f).flatten.length = xs.length * c := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_cons]
    rw [hEach x (.head _), ih (fun y hy => hEach y (.tail _ hy)), Nat.succ_mul]
    omega

/-- Structured acceptance implies the exact Algorithm 20 wire length; nested checks
also exclude compensating overlong and short vectors with the same total byte count. -/
theorem slhVerifyInternal_encoded_length (p : Fips205Params) (msg : List UInt8)
    (sig : SlhSignature) (pk : SlhPublicKey)
    (h : slhVerifyInternal p msg sig pk = true) :
    (encodeSlhSig sig).length = p.sigBytes := by
  obtain ⟨hr, hf, hh, hfs, hhs⟩ := slhVerifyInternal_shapes p msg sig pk h
  have flatLen (xs : List (List UInt8)) (n : Nat)
      (hw : xs.all (fun x => decide (x.length = n)) = true) :
      xs.flatten.length = xs.length * n := by
    have he : ∀ x ∈ xs, (id x).length = n := by
      simpa only [List.all_eq_true, decide_eq_true_eq, id_eq] using hw
    simpa using flatten_map_fixed_len xs id n he
  have hfb : (sig.forsSig.map fun f => f.skVal ++ f.authPath.flatten).flatten.length =
      p.k * (1 + p.a) * p.n := by
    rw [flatten_map_fixed_len sig.forsSig _ ((1 + p.a) * p.n)]
    · rw [hf, Nat.mul_assoc]
    · intro f hmem
      have hw := List.all_eq_true.mp hfs f hmem
      simp only [fipsForsSigShape, Bool.and_eq_true, decide_eq_true_eq] at hw
      rw [List.length_append, hw.1.1, flatLen _ _ hw.2, hw.1.2]
      simp [Nat.add_mul]
  have hhb : (sig.htSig.map fun x => x.wotsSig.flatten ++ x.authPath.flatten).flatten.length =
      p.d * (p.ell + p.hp) * p.n := by
    rw [flatten_map_fixed_len sig.htSig _ ((p.ell + p.hp) * p.n)]
    · rw [hh, Nat.mul_assoc]
    · intro x hmem
      have hw := List.all_eq_true.mp hhs x hmem
      simp only [fipsXmssSigShape, Bool.and_eq_true, decide_eq_true_eq] at hw
      rw [List.length_append, flatLen _ _ hw.1.1.2, flatLen _ _ hw.2,
        hw.1.1.1, hw.1.2, Nat.add_mul]
  simp only [encodeSlhSig, List.length_append, hr, hfb, hhb, Fips205Params.sigBytes]

theorem encodeSlhSig_slhSignInternal_length (p : Fips205Params)
    (msgPrime : List UInt8) (sk : SlhSecretKey) (optRand : List UInt8) :
    (encodeSlhSig (slhSignInternal p msgPrime sk optRand)).length = p.sigBytes := by
  unfold encodeSlhSig slhSignInternal Fips205Params.sigBytes
  dsimp only
  simp only [List.length_append]
  have hR : (fipsPrfMsg p.n sk.skPrf optRand msgPrime).length = p.n := shake256Xof_length p.n _
  let split := fipsSplitDigest p (fipsHMsg p.m (fipsPrfMsg p.n sk.skPrf optRand msgPrime) sk.pkSeed sk.pkRoot msgPrime)
  let fs := fipsForsSign p split.1 sk.skSeed sk.pkSeed split.2.1 split.2.2
  have hFsLen : fs.length = p.k := by simp [fs, fipsForsSign]
  have hForsBytes : (fs.map fun f => f.skVal ++ f.authPath.flatten).flatten.length = p.k * (1 + p.a) * p.n := by
    rw [flatten_map_fixed_len fs _ ((1 + p.a) * p.n)]
    · rw [hFsLen, Nat.mul_assoc]
    · intro f hf
      simp only [fs, fipsForsSign, List.mem_map] at hf
      obtain ⟨j, _, rfl⟩ := hf
      simp only [List.length_append, fipsPrf_length]
      have hAuthNodes : ∀ (z nodeIdx localIdx : Nat),
          ((fipsForsAuthPath p sk.skSeed sk.pkSeed split.2.1 split.2.2 z nodeIdx localIdx).flatten).length = z * p.n := by
        intro z
        induction z with
        | zero => simp [fipsForsAuthPath]
        | succ z ih =>
          intro nodeIdx localIdx
          simp only [fipsForsAuthPath]
          have hNodeLen : ∀ (zz ni : Nat), (fipsForsNode p sk.skSeed sk.pkSeed split.2.1 split.2.2 zz ni).length = p.n := by
            intro zz; induction zz with
            | zero => intro _; simp [fipsForsNode]
            | succ _ _ => intro _; simp [fipsForsNode]
          split
          · simp [List.flatten_append, ih, hNodeLen, Nat.succ_mul]
          · simp [List.flatten_append, ih, hNodeLen, Nat.succ_mul]
      rw [hAuthNodes, Nat.add_mul, Nat.one_mul]
  let pkFors := fipsForsPkFromSig p fs split.1 sk.pkSeed split.2.1 split.2.2
  let hs := fipsHtSignAux p sk.skSeed sk.pkSeed 0 split.2.1 split.2.2 pkFors p.d
  have hHsLen : hs.length = p.d := fipsHtSignAux_length p sk.skSeed sk.pkSeed p.d 0 _ _ _
  have hHtBytes : (hs.map fun x => x.wotsSig.flatten ++ x.authPath.flatten).flatten.length = p.d * (p.ell + p.hp) * p.n := by
    have hXmssMem : ∀ (rem layer it il : Nat) (cm : List UInt8) (x : FipsXmssSig),
        x ∈ fipsHtSignAux p sk.skSeed sk.pkSeed layer it il cm rem →
        (x.wotsSig.flatten ++ x.authPath.flatten).length = (p.ell + p.hp) * p.n := by
      intro rem
      induction rem with
      | zero => intros _ _ _ _ _ hMem; cases hMem
      | succ rem ih =>
        intro layer it il cm x hMem
        simp only [fipsHtSignAux, List.mem_cons] at hMem
        rcases hMem with rfl | hTail
        · simp only [fipsXmssSign, List.length_append]
          have hWots : ((fipsWotsSign p cm sk.skSeed sk.pkSeed layer it il).flatten).length = p.ell * p.n := by
            unfold fipsWotsSign
            have h1 := flatten_map_fixed_len (List.range p.ell)
              (fun i => fipsChain p.n sk.pkSeed layer it il i 0 ((fipsWotsDigits p.ell1 cm).getD i 0)
                (fipsPrf p.n sk.pkSeed sk.skSeed (mkFipsAdrs layer it .wotsPrf il i 0))) p.n
              (fun i _ => fipsChain_length _ _ _ _ _ _ _ _ _ (fipsPrf_length _ _ _ _))
            simpa using h1
          have hAuth : ∀ (z ni li : Nat),
              ((fipsXmssAuthPath p sk.skSeed sk.pkSeed layer it z ni li).flatten).length = z * p.n := by
            intro z; induction z with
            | zero => simp [fipsXmssAuthPath]
            | succ z ihz =>
              intro ni li
              have hNLen : ∀ (zz nni : Nat), (fipsXmssNode p sk.skSeed sk.pkSeed layer it zz nni).length = p.n := by
                intro zz; induction zz with
                | zero => intro _; simp [fipsXmssNode, fipsWotsPkGen]
                | succ _ _ => intro _; simp [fipsXmssNode]
              simp only [fipsXmssAuthPath]
              split
              · simp [List.flatten_append, ihz, hNLen, Nat.succ_mul]
              · simp [List.flatten_append, ihz, hNLen, Nat.succ_mul]
          rw [hWots, hAuth, Nat.add_mul]
        · exact ih _ _ _ _ x hTail
    rw [flatten_map_fixed_len hs _ ((p.ell + p.hp) * p.n) (fun x hx => hXmssMem p.d 0 _ _ _ x hx),
        hHsLen, Nat.mul_assoc]
  rw [hR, hForsBytes, hHtBytes]

/-- Explicit `SHAKE256` collision witness on an `n`-byte NIST FIPS 205 tweakable hash call. -/
structure Fips205ShakeCollision (n : Nat) where
  in1  : List UInt8
  in2  : List UInt8
  hNe  : in1 ≠ in2
  hEq  : shake256Xof n in1 = shake256Xof n in2

/-- Explicit WOTS+ chain-preimage inversion witness strictly upstream of the honest revealed step `d₁`:
    exhibits `preimage` at step `d₁ - 1 < d₁` hashing directly into the honest signature element `honSigAtIdx`. -/
structure Fips205ChainPreimageBreak (p : Fips205Params) (pkSeed skSeed msg₁ : List UInt8)
    (layer tree kp : Nat) where
  chainIdx   : Nat
  hChainLt   : chainIdx < p.ell
  d1         : Nat
  hD1Eq      : d1 = (fipsWotsDigits p.ell1 msg₁).getD chainIdx 0
  hD1Pos     : 0 < d1
  preimage   : List UInt8
  hInverts   :
    fipsF p.n pkSeed (mkFipsAdrs layer tree .wotsHash kp chainIdx (d1 - 1)) preimage =
      fipsChain p.n pkSeed layer tree kp chainIdx 0 d1
        (fipsPrf p.n pkSeed skSeed (mkFipsAdrs layer tree .wotsPrf kp chainIdx 0))

private theorem flatten_inj_fixed_len {n : Nat} (hn : 0 < n) :
    ∀ {xs ys : List (List UInt8)},
      xs.length = ys.length →
      (∀ x ∈ xs, x.length = n) →
      (∀ y ∈ ys, y.length = n) →
      xs.flatten = ys.flatten →
      xs = ys
  | [], [], _, _, _, _ => rfl
  | x :: xs, y :: ys, hLen, hX, hY, hFlat => by
    simp only [List.flatten_cons] at hFlat
    have hxL : x.length = n := hX x (.head _)
    have hyL : y.length = n := hY y (.head _)
    obtain ⟨hxy, hRest⟩ := List.append_inj hFlat (hxL.trans hyL.symm)
    have _ := hn
    rw [hxy, flatten_inj_fixed_len hn (Nat.succ.inj hLen)
      (fun a ha => hX a (.tail _ ha)) (fun b hb => hY b (.tail _ hb)) hRest]

private def extractFipsChainCollision (n : Nat) (pkSeed : List UInt8) (layer tree kp chainIdx : Nat) :
    (steps startIdx : Nat) → (u v : List UInt8) →
    u ≠ v →
    fipsChain n pkSeed layer tree kp chainIdx startIdx steps u =
      fipsChain n pkSeed layer tree kp chainIdx startIdx steps v →
    Fips205ShakeCollision n
  | 0, _, _, _, hNe, hEq => False.elim (hNe hEq)
  | steps + 1, startIdx, u, v, hNe, hEq =>
    let adrs := mkFipsAdrs layer tree .wotsHash kp chainIdx startIdx
    let fu := fipsF n pkSeed adrs u
    let fv := fipsF n pkSeed adrs v
    if hStep : fu = fv then
      { in1 := pkSeed ++ encodeFips205Adrs adrs ++ u
        in2 := pkSeed ++ encodeFips205Adrs adrs ++ v
        hNe := fun hIn => by
          simp only [List.append_assoc, List.append_cancel_left_eq] at hIn
          exact hNe hIn
        hEq := hStep }
    else
      extractFipsChainCollision n pkSeed layer tree kp chainIdx steps (startIdx + 1) fu fv hStep hEq

/-- **Constructive NIST FIPS 205 WOTS+ Forgery Extractor (`extractFips205WotsForgery`)**:
    Zero-`Classical.choice` `Type`-valued `PSum` extractor proving that ANY forged WOTS+ signature `sig₂`
    for `msg₂ ≠ msg₁` verifying against `fipsWotsPkGen p skSeed pkSeed layer tree kp` constructively yields:
    - `PSum.inl`: an explicit `SHAKE256` collision (`in1 ≠ in2` with identical `n`-byte digest), OR
    - `PSum.inr`: an explicit preimage inverting `fipsF` at step `d₁ - 1` strictly before the
      honest revealed chain value at `d₁`! -/
def extractFips205WotsForgery (p : Fips205Params) (hnPos : 0 < p.n) (hnLe : p.n ≤ 128)
    (pkSeed skSeed msg₁ msg₂ : List UInt8) (layer tree kp : Nat)
    (sig₂ : List (List UInt8))
    (hMsg₁ : msg₁.length = p.n) (hMsg₂ : msg₂.length = p.n) (hNe : msg₁ ≠ msg₂)
    (hSigElemLen : ∀ i : Nat, i < p.ell → (sig₂.getD i []).length = p.n)
    (hForge : fipsWotsPkFromSig p sig₂ msg₂ pkSeed layer tree kp =
              fipsWotsPkGen p skSeed pkSeed layer tree kp) :
    PSum (Fips205ShakeCollision p.n)
         (Fips205ChainPreimageBreak p pkSeed skSeed msg₁ layer tree kp) :=
  let digits₂ := fipsWotsDigits p.ell1 msg₂
  let tmp₂ := (List.range p.ell).map fun i =>
    let di := digits₂.getD i 0
    fipsChain p.n pkSeed layer tree kp i di (15 - di) (sig₂.getD i [])
  let tmpHon := (List.range p.ell).map fun i =>
    let sk := fipsPrf p.n pkSeed skSeed (mkFipsAdrs layer tree .wotsPrf kp i 0)
    fipsChain p.n pkSeed layer tree kp i 0 15 sk
  let adrsPk := mkFipsAdrs layer tree .wotsPk kp 0 0
  if hTmpNe : tmp₂ ≠ tmpHon then
    .inl
      { in1 := pkSeed ++ encodeFips205Adrs adrsPk ++ tmp₂.flatten
        in2 := pkSeed ++ encodeFips205Adrs adrsPk ++ tmpHon.flatten
        hNe := fun hIn => by
          simp only [List.append_assoc, List.append_cancel_left_eq] at hIn
          have hT2Len : ∀ x ∈ tmp₂, x.length = p.n := by
            intro x hx
            simp only [tmp₂, List.mem_map, List.mem_range] at hx
            obtain ⟨i, hi, rfl⟩ := hx
            exact fipsChain_length _ _ _ _ _ _ _ _ _ (hSigElemLen i hi)
          have hTHLen : ∀ y ∈ tmpHon, y.length = p.n := by
            intro y hy
            simp only [tmpHon, List.mem_map, List.mem_range] at hy
            obtain ⟨i, _, rfl⟩ := hy
            exact fipsChain_length _ _ _ _ _ _ _ _ _ (fipsPrf_length _ _ _ _)
          exact hTmpNe (flatten_inj_fixed_len hnPos (by simp [tmp₂, tmpHon]) hT2Len hTHLen hIn)
        hEq := hForge }
  else
    have hTmpEq : tmp₂ = tmpHon := Decidable.of_not_not hTmpNe
    let bw := findFipsWotsBackwardIdx msg₁ msg₂ hnLe hMsg₁ hMsg₂ hNe
    let idx := bw.idx
    have h1 := bw.h1
    have h2 := bw.h2
    have hBack := bw.hLt
    have hIdxEll : idx < p.ell := by
      have hw1Len := (fipsWotsDigits_bounds (2 * p.n) msg₁).1
      unfold Fips205Params.ell
      omega
    let d1 := (fipsWotsDigits p.ell1 msg₁).getD idx 0
    let d2 := (fipsWotsDigits p.ell1 msg₂).getD idx 0
    have hd1EqElem : d1 = (fipsWotsDigits (2 * p.n) msg₁)[idx]'h1 := by
      dsimp only [d1, Fips205Params.ell1]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]; rfl
    have hd2EqElem : d2 = (fipsWotsDigits (2 * p.n) msg₂)[idx]'h2 := by
      dsimp only [d2, Fips205Params.ell1]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]; rfl
    have hd2LtD1 : d2 < d1 := hd2EqElem.symm ▸ hd1EqElem.symm ▸ hBack
    have hd1Lt16 : d1 < 16 :=
      hd1EqElem ▸ (fipsWotsDigits_bounds (2 * p.n) msg₁).2 _ (List.getElem_mem h1)
    let skIdx := fipsPrf p.n pkSeed skSeed (mkFipsAdrs layer tree .wotsPrf kp idx 0)
    let advAtD1 := fipsChain p.n pkSeed layer tree kp idx d2 (d1 - d2) (sig₂.getD idx [])
    let honAtD1 := fipsChain p.n pkSeed layer tree kp idx 0 d1 skIdx
    if hAdvEqHon : advAtD1 = honAtD1 then
      let pre := fipsChain p.n pkSeed layer tree kp idx d2 (d1 - 1 - d2) (sig₂.getD idx [])
      .inr
        { chainIdx := idx
          hChainLt := hIdxEll
          d1       := d1
          hD1Eq    := rfl
          hD1Pos   := by omega
          preimage := pre
          hInverts := by
            have hSplit : d1 - d2 = (d1 - 1 - d2) + 1 := by omega
            have hComp := fipsChain_add p.n pkSeed layer tree kp idx (d1 - 1 - d2) 1 d2 (sig₂.getD idx [])
            have hStart : d2 + (d1 - 1 - d2) = d1 - 1 := by omega
            have hStep1 : fipsChain p.n pkSeed layer tree kp idx (d1 - 1) 1 pre =
                fipsF p.n pkSeed (mkFipsAdrs layer tree .wotsHash kp idx (d1 - 1)) pre := rfl
            calc fipsF p.n pkSeed (mkFipsAdrs layer tree .wotsHash kp idx (d1 - 1)) pre
              _ = fipsChain p.n pkSeed layer tree kp idx (d2 + (d1 - 1 - d2)) 1 pre := by
                    rw [hStart, hStep1]
              _ = fipsChain p.n pkSeed layer tree kp idx d2 ((d1 - 1 - d2) + 1) (sig₂.getD idx []) :=
                    hComp
              _ = advAtD1 := by dsimp only [advAtD1]; rw [← hSplit]
              _ = honAtD1 := hAdvEqHon }
    else
      have hCoordEq : tmp₂.getD idx [] = tmpHon.getD idx [] := congrArg (·.getD idx []) hTmpEq
      have hEndEq : fipsChain p.n pkSeed layer tree kp idx d1 (15 - d1) advAtD1 =
                    fipsChain p.n pkSeed layer tree kp idx d1 (15 - d1) honAtD1 := by
        have hLhs : tmp₂.getD idx [] = fipsChain p.n pkSeed layer tree kp idx d2 (15 - d2) (sig₂.getD idx []) :=
          list_getD_map_range_fips p.ell _ [] hIdxEll
        have hRhs : tmpHon.getD idx [] = fipsChain p.n pkSeed layer tree kp idx 0 15 skIdx :=
          list_getD_map_range_fips p.ell _ [] hIdxEll
        have hAdvSplit : fipsChain p.n pkSeed layer tree kp idx d1 (15 - d1) advAtD1 =
            fipsChain p.n pkSeed layer tree kp idx d2 (15 - d2) (sig₂.getD idx []) := by
          dsimp only [advAtD1]
          have hc := fipsChain_add p.n pkSeed layer tree kp idx (d1 - d2) (15 - d1) d2 (sig₂.getD idx [])
          have h1 : d2 + (d1 - d2) = d1 := by omega
          have h2 : (d1 - d2) + (15 - d1) = 15 - d2 := by omega
          rw [h1, h2] at hc
          exact hc
        have hHonSplit : fipsChain p.n pkSeed layer tree kp idx d1 (15 - d1) honAtD1 =
            fipsChain p.n pkSeed layer tree kp idx 0 15 skIdx := by
          dsimp only [honAtD1]
          have hc := fipsChain_add p.n pkSeed layer tree kp idx d1 (15 - d1) 0 skIdx
          have h2 : d1 + (15 - d1) = 15 := by omega
          simpa [h2] using hc
        rw [hAdvSplit, hHonSplit, ← hLhs, ← hRhs, hCoordEq]
      .inl (extractFipsChainCollision p.n pkSeed layer tree kp idx (15 - d1) d1 advAtD1 honAtD1 hAdvEqHon hEndEq)

/-- Distributed MPC oracle interface for NIST FIPS 205 `SLH-DSA`:
    `SK.seed` and `SK.prf` remain secret-shared across the MPC committee and are NEVER
    reconstructed in cleartext; only public outputs at the `Depth = 1 + w` cut are opened! -/
structure SlhMpcOracles where
  /-- Evaluates `PRF_msg(SK.prf, opt_rand, M')` over shares and opens ONLY public randomizer `R`. -/
  evalPrfMsg       : List UInt8 → List UInt8 → List UInt8
  /-- Evaluates `chain(PRF(PK.seed, SK.seed, wotsPrfAdrs), 0, steps)` inside MPC (`Depth = 1 + steps ≤ 16`)
      and opens ONLY the selected chain value at `steps` (`steps = d_i` or public endpoint `15`). -/
  evalWotsChainEnd : Nat → Nat → Nat → Nat → Nat → List UInt8
  /-- Evaluates `PRF(PK.seed, SK.seed, forsPrfAdrs)` inside MPC and opens ONLY the `k` signature-disclosed FORS leaves. -/
  evalForsReveal   : Nat → Nat → Nat → List UInt8
  /-- Evaluates `F(PK.seed, forsTreeAdrs, PRF(PK.seed, SK.seed, forsPrfAdrs))` inside MPC (`Depth = 2`)
      and opens ONLY the public FORS leaf hash (unqueried FORS secret values are never opened). -/
  evalForsLeafHash : Nat → Nat → Nat → List UInt8

/-- Soundness predicate stating that a distributed `SlhMpcOracles` instance faithfully evaluates
    the 4 public-output cut boundary functions of `(skSeed, skPrf, pkSeed)`. -/
def SlhMpcOracles.MatchesKey (o : SlhMpcOracles) (p : Fips205Params)
    (skSeed skPrf pkSeed : List UInt8) : Prop :=
  (∀ optRand msgPrime, o.evalPrfMsg optRand msgPrime = fipsPrfMsg p.n skPrf optRand msgPrime) ∧
  (∀ layer tree kp chainIdx steps,
    o.evalWotsChainEnd layer tree kp chainIdx steps =
      fipsChain p.n pkSeed layer tree kp chainIdx 0 steps
        (fipsPrf p.n pkSeed skSeed (mkFipsAdrs layer tree .wotsPrf kp chainIdx 0))) ∧
  (∀ tree idxLeaf globalLeaf,
    o.evalForsReveal tree idxLeaf globalLeaf =
      fipsPrf p.n pkSeed skSeed (mkFipsAdrs 0 tree .forsPrf idxLeaf 0 globalLeaf)) ∧
  (∀ tree idxLeaf nodeIdx,
    o.evalForsLeafHash tree idxLeaf nodeIdx =
      fipsF p.n pkSeed (mkFipsAdrs 0 tree .forsTree idxLeaf 0 nodeIdx)
        (fipsPrf p.n pkSeed skSeed (mkFipsAdrs 0 tree .forsPrf idxLeaf 0 nodeIdx)))

theorem SlhMpcOracles.MatchesKey_eq (o : SlhMpcOracles) (p : Fips205Params)
    (skSeed skPrf pkSeed : List UInt8) :
    o.MatchesKey p skSeed skPrf pkSeed =
      ((∀ optRand msgPrime, o.evalPrfMsg optRand msgPrime = fipsPrfMsg p.n skPrf optRand msgPrime) ∧
       (∀ layer tree kp chainIdx steps,
         o.evalWotsChainEnd layer tree kp chainIdx steps =
           fipsChain p.n pkSeed layer tree kp chainIdx 0 steps
             (fipsPrf p.n pkSeed skSeed (mkFipsAdrs layer tree .wotsPrf kp chainIdx 0))) ∧
       (∀ tree idxLeaf globalLeaf,
         o.evalForsReveal tree idxLeaf globalLeaf =
           fipsPrf p.n pkSeed skSeed (mkFipsAdrs 0 tree .forsPrf idxLeaf 0 globalLeaf)) ∧
       (∀ tree idxLeaf nodeIdx,
         o.evalForsLeafHash tree idxLeaf nodeIdx =
           fipsF p.n pkSeed (mkFipsAdrs 0 tree .forsTree idxLeaf 0 nodeIdx)
             (fipsPrf p.n pkSeed skSeed (mkFipsAdrs 0 tree .forsPrf idxLeaf 0 nodeIdx)))) := by rfl

def mpcWotsPkGen (p : Fips205Params) (o : SlhMpcOracles) (pkSeed : List UInt8)
    (layer tree kp : Nat) : List UInt8 :=
  let tmp := (List.range p.ell).map fun i => o.evalWotsChainEnd layer tree kp i 15
  fipsTl p.n pkSeed (mkFipsAdrs layer tree .wotsPk kp 0 0) tmp

def mpcWotsSign (p : Fips205Params) (o : SlhMpcOracles) (msg : List UInt8)
    (layer tree kp : Nat) : List (List UInt8) :=
  let digits := fipsWotsDigits p.ell1 msg
  (List.range p.ell).map fun i => o.evalWotsChainEnd layer tree kp i (digits.getD i 0)

def mpcXmssNode (p : Fips205Params) (o : SlhMpcOracles) (pkSeed : List UInt8)
    (layer tree : Nat) : Nat → Nat → List UInt8
  | 0, nodeIdx => mpcWotsPkGen p o pkSeed layer tree nodeIdx
  | z + 1, nodeIdx =>
    let lnode := mpcXmssNode p o pkSeed layer tree z (2 * nodeIdx)
    let rnode := mpcXmssNode p o pkSeed layer tree z (2 * nodeIdx + 1)
    fipsH p.n pkSeed (mkFipsAdrs layer tree .tree 0 (z + 1) nodeIdx) lnode rnode

def mpcXmssAuthPath (p : Fips205Params) (o : SlhMpcOracles) (pkSeed : List UInt8)
    (layer tree : Nat) : Nat → Nat → Nat → List (List UInt8)
  | 0, _, _ => []
  | z + 1, nodeIdx, localIdx =>
    let half := 2 ^ z
    if localIdx < half then
      let rnode := mpcXmssNode p o pkSeed layer tree z (2 * nodeIdx + 1)
      mpcXmssAuthPath p o pkSeed layer tree z (2 * nodeIdx) localIdx ++ [rnode]
    else
      let lnode := mpcXmssNode p o pkSeed layer tree z (2 * nodeIdx)
      mpcXmssAuthPath p o pkSeed layer tree z (2 * nodeIdx + 1) (localIdx - half) ++ [lnode]

def mpcForsNode (p : Fips205Params) (o : SlhMpcOracles) (pkSeed : List UInt8)
    (tree idxLeaf : Nat) : Nat → Nat → List UInt8
  | 0, nodeIdx => o.evalForsLeafHash tree idxLeaf nodeIdx
  | z + 1, nodeIdx =>
    let lnode := mpcForsNode p o pkSeed tree idxLeaf z (2 * nodeIdx)
    let rnode := mpcForsNode p o pkSeed tree idxLeaf z (2 * nodeIdx + 1)
    fipsH p.n pkSeed (mkFipsAdrs 0 tree .forsTree idxLeaf (z + 1) nodeIdx) lnode rnode

def mpcForsAuthPath (p : Fips205Params) (o : SlhMpcOracles) (pkSeed : List UInt8)
    (tree idxLeaf : Nat) : Nat → Nat → Nat → List (List UInt8)
  | 0, _, _ => []
  | z + 1, nodeIdx, localIdx =>
    let half := 2 ^ z
    if localIdx < half then
      let rnode := mpcForsNode p o pkSeed tree idxLeaf z (2 * nodeIdx + 1)
      mpcForsAuthPath p o pkSeed tree idxLeaf z (2 * nodeIdx) localIdx ++ [rnode]
    else
      let lnode := mpcForsNode p o pkSeed tree idxLeaf z (2 * nodeIdx)
      mpcForsAuthPath p o pkSeed tree idxLeaf z (2 * nodeIdx + 1) (localIdx - half) ++ [lnode]

def mpcForsSign (p : Fips205Params) (o : SlhMpcOracles) (md pkSeed : List UInt8)
    (tree idxLeaf : Nat) : List FipsForsTreeSig :=
  let indices := base2b md p.a p.k
  (List.range p.k).map fun j =>
    let idxJ := indices.getD j 0
    let globalLeaf := j * (2 ^ p.a) + idxJ
    { skVal    := o.evalForsReveal tree idxLeaf globalLeaf
      authPath := mpcForsAuthPath p o pkSeed tree idxLeaf p.a j idxJ }

def mpcHtSignAux (p : Fips205Params) (o : SlhMpcOracles) (pkSeed : List UInt8) :
    Nat → Nat → Nat → List UInt8 → Nat → List FipsXmssSig
  | _, _, _, _, 0 => []
  | layer, idxTree, idxLeaf, curMsg, rem + 1 =>
    let sigTmp : FipsXmssSig :=
      { wotsSig  := mpcWotsSign p o curMsg layer idxTree idxLeaf
        authPath := mpcXmssAuthPath p o pkSeed layer idxTree p.hp 0 idxLeaf }
    let root := mpcXmssNode p o pkSeed layer idxTree p.hp 0
    let nextLeaf := idxTree % (2 ^ p.hp)
    let nextTree := idxTree / (2 ^ p.hp)
    sigTmp :: mpcHtSignAux p o pkSeed (layer + 1) nextTree nextLeaf root rem

/-- Distributed MPC `SLH-DSA` key generation (`PK.root` derived solely via public chain-15 openings;
    `SK.seed` and `SK.prf` are NEVER reconstructed in cleartext!). -/
def slhKeygenMpc (p : Fips205Params) (o : SlhMpcOracles) (pkSeed : List UInt8) : SlhPublicKey :=
  { pkSeed := pkSeed, pkRoot := mpcXmssNode p o pkSeed (p.d - 1) 0 p.hp 0 }

/-- Distributed MPC `SLH-DSA` signing (`slhSignMpc`): takes ONLY `o : SlhMpcOracles` and public `pk`
    (never receiving or reconstructing `SlhSecretKey`!). -/
def slhSignMpc (p : Fips205Params) (o : SlhMpcOracles) (msgPrime : List UInt8)
    (pk : SlhPublicKey) (optRand : List UInt8) : SlhSignature :=
  let rRand := o.evalPrfMsg optRand msgPrime
  let digest := fipsHMsg p.m rRand pk.pkSeed pk.pkRoot msgPrime
  let (md, idxTree, idxLeaf) := fipsSplitDigest p digest
  let forsSig := mpcForsSign p o md pk.pkSeed idxTree idxLeaf
  let pkFors := fipsForsPkFromSig p forsSig md pk.pkSeed idxTree idxLeaf
  let htSig := mpcHtSignAux p o pk.pkSeed 0 idxTree idxLeaf pkFors p.d
  { rRand := rRand, forsSig := forsSig, htSig := htSig }

/-- Flat wire-encoded threshold FIPS 205 signature (`17,088`B for `128f`, `7,856`B for `128s`). -/
def thresholdSlhSignBytes (p : Fips205Params) (o : SlhMpcOracles) (msgPrime : List UInt8)
    (pk : SlhPublicKey) (optRand : List UInt8) : List UInt8 :=
  encodeSlhSig (slhSignMpc p o msgPrime pk optRand)

private theorem mpcXmssNode_eq_fipsXmssNode (p : Fips205Params) (o : SlhMpcOracles)
    (skSeed skPrf pkSeed : List UInt8) (hMatch : o.MatchesKey p skSeed skPrf pkSeed)
    (layer tree : Nat) :
    ∀ (z nodeIdx : Nat), mpcXmssNode p o pkSeed layer tree z nodeIdx = fipsXmssNode p skSeed pkSeed layer tree z nodeIdx
  | 0, nodeIdx => by
    simp [mpcXmssNode, fipsXmssNode, mpcWotsPkGen, fipsWotsPkGen, hMatch.2.1]
  | z + 1, nodeIdx => by
    simp [mpcXmssNode, fipsXmssNode,
      mpcXmssNode_eq_fipsXmssNode p o skSeed skPrf pkSeed hMatch layer tree z]

private theorem mpcXmssAuthPath_eq_fipsXmssAuthPath (p : Fips205Params) (o : SlhMpcOracles)
    (skSeed skPrf pkSeed : List UInt8) (hMatch : o.MatchesKey p skSeed skPrf pkSeed)
    (layer tree : Nat) :
    ∀ (z nodeIdx localIdx : Nat),
      mpcXmssAuthPath p o pkSeed layer tree z nodeIdx localIdx =
        fipsXmssAuthPath p skSeed pkSeed layer tree z nodeIdx localIdx
  | 0, _, _ => rfl
  | z + 1, nodeIdx, localIdx => by
    simp only [mpcXmssAuthPath, fipsXmssAuthPath]
    split <;> simp [mpcXmssAuthPath_eq_fipsXmssAuthPath p o skSeed skPrf pkSeed hMatch layer tree z,
                    mpcXmssNode_eq_fipsXmssNode p o skSeed skPrf pkSeed hMatch layer tree z]

private theorem mpcForsNode_eq_fipsForsNode (p : Fips205Params) (o : SlhMpcOracles)
    (skSeed skPrf pkSeed : List UInt8) (hMatch : o.MatchesKey p skSeed skPrf pkSeed)
    (tree idxLeaf : Nat) :
    ∀ (z nodeIdx : Nat), mpcForsNode p o pkSeed tree idxLeaf z nodeIdx = fipsForsNode p skSeed pkSeed tree idxLeaf z nodeIdx
  | 0, nodeIdx => by simp [mpcForsNode, fipsForsNode, hMatch.2.2.2]
  | z + 1, nodeIdx => by
    simp [mpcForsNode, fipsForsNode,
      mpcForsNode_eq_fipsForsNode p o skSeed skPrf pkSeed hMatch tree idxLeaf z]

private theorem mpcForsAuthPath_eq_fipsForsAuthPath (p : Fips205Params) (o : SlhMpcOracles)
    (skSeed skPrf pkSeed : List UInt8) (hMatch : o.MatchesKey p skSeed skPrf pkSeed)
    (tree idxLeaf : Nat) :
    ∀ (z nodeIdx localIdx : Nat),
      mpcForsAuthPath p o pkSeed tree idxLeaf z nodeIdx localIdx =
        fipsForsAuthPath p skSeed pkSeed tree idxLeaf z nodeIdx localIdx
  | 0, _, _ => rfl
  | z + 1, nodeIdx, localIdx => by
    simp only [mpcForsAuthPath, fipsForsAuthPath]
    split <;> simp [mpcForsAuthPath_eq_fipsForsAuthPath p o skSeed skPrf pkSeed hMatch tree idxLeaf z,
                    mpcForsNode_eq_fipsForsNode p o skSeed skPrf pkSeed hMatch tree idxLeaf z]

private theorem mpcHtSignAux_eq_fipsHtSignAux (p : Fips205Params) (o : SlhMpcOracles)
    (skSeed skPrf pkSeed : List UInt8) (hMatch : o.MatchesKey p skSeed skPrf pkSeed) :
    ∀ (rem layer idxTree idxLeaf : Nat) (curMsg : List UInt8),
      mpcHtSignAux p o pkSeed layer idxTree idxLeaf curMsg rem =
        fipsHtSignAux p skSeed pkSeed layer idxTree idxLeaf curMsg rem
  | 0, _, _, _, _ => rfl
  | rem + 1, layer, idxTree, idxLeaf, curMsg => by
    simp [mpcHtSignAux, fipsHtSignAux, mpcWotsSign, fipsWotsSign, fipsXmssSign, hMatch.2.1,
      mpcXmssAuthPath_eq_fipsXmssAuthPath p o skSeed skPrf pkSeed hMatch,
      mpcXmssNode_eq_fipsXmssNode p o skSeed skPrf pkSeed hMatch,
      mpcHtSignAux_eq_fipsHtSignAux p o skSeed skPrf pkSeed hMatch rem]

/-- **Threshold-to-Standard FIPS 205 Bit-Identity (`thresholdSlhSign_eq_slhSignInternal`)**:
    Whenever the distributed MPC engine `o : SlhMpcOracles` faithfully evaluates the 4 cut-boundary
    oracles (`hMatch : o.MatchesKey p skSeed skPrf pkSeed` — proved in `ThresholdMpc.lean` for
    share-level `mpcShake256XofRss` without EVER reconstructing `skSeed` or `skPrf`!),
    `slhKeygenMpc` and `thresholdSlhSignBytes` emit the **bit-for-bit identical** public key and
    `17,088`-byte (`128f`) / `7,856`-byte (`128s`) signature as single-party NIST FIPS 205! -/
theorem thresholdSlhSign_eq_slhSignInternal (p : Fips205Params) (hWf : p.wellFormed = true)
    (o : SlhMpcOracles) (skSeed skPrf pkSeed msgPrime optRand : List UInt8)
    (hMatch : o.MatchesKey p skSeed skPrf pkSeed) :
    let (sk, pk) := slhKeygenInternal p skSeed skPrf pkSeed
    slhKeygenMpc p o pkSeed = pk ∧
    slhSignMpc p o msgPrime pk optRand = slhSignInternal p msgPrime sk optRand ∧
    thresholdSlhSignBytes p o msgPrime pk optRand =
      encodeSlhSig (slhSignInternal p msgPrime sk optRand) ∧
    (thresholdSlhSignBytes p o msgPrime pk optRand).length = p.sigBytes ∧
    slhVerifyInternal p msgPrime (slhSignMpc p o msgPrime pk optRand) pk = true := by
  have hRoot : slhKeygenMpc p o pkSeed = (slhKeygenInternal p skSeed skPrf pkSeed).2 := by
    simp [slhKeygenMpc, slhKeygenInternal,
      mpcXmssNode_eq_fipsXmssNode p o skSeed skPrf pkSeed hMatch]
  have hSig : slhSignMpc p o msgPrime (slhKeygenInternal p skSeed skPrf pkSeed).2 optRand =
      slhSignInternal p msgPrime (slhKeygenInternal p skSeed skPrf pkSeed).1 optRand := by
    dsimp only [slhKeygenInternal, slhSignMpc, slhSignInternal]
    have hR : o.evalPrfMsg optRand msgPrime = fipsPrfMsg p.n skPrf optRand msgPrime := hMatch.1 _ _
    have hFors : ∀ md t l, mpcForsSign p o md pkSeed t l = fipsForsSign p md skSeed pkSeed t l := by
      intros md t l
      simp [mpcForsSign, fipsForsSign, hMatch.2.2.1,
        mpcForsAuthPath_eq_fipsForsAuthPath p o skSeed skPrf pkSeed hMatch]
    simp only [hR, hFors, mpcHtSignAux_eq_fipsHtSignAux p o skSeed skPrf pkSeed hMatch]
  refine ⟨hRoot, hSig, ?_, ?_, ?_⟩
  · unfold thresholdSlhSignBytes
    dsimp only [slhKeygenInternal] at hSig ⊢
    rw [hSig]
  · unfold thresholdSlhSignBytes
    dsimp only [slhKeygenInternal] at hSig ⊢
    rw [hSig]
    exact encodeSlhSig_slhSignInternal_length p msgPrime _ optRand
  · dsimp only [slhKeygenInternal] at hSig ⊢
    rw [hSig]
    exact slhVerifyInternal_slhSignInternal p hWf skSeed skPrf pkSeed msgPrime optRand

/-- Accepted prehash encodings enforce the advertised security category. -/
theorem accepted_preHash_category (p : Fips205Params) (alg : FipsPreHashAlg)
    (ctx digest encoded : List UInt8)
    (h : encodePreHashMsgPrime p alg ctx digest = some encoded) :
    preHashCompatible p alg = true := by
  unfold encodePreHashMsgPrime at h
  split at h
  · cases h
  · rename_i hn
    cases hc : preHashCompatible p alg <;> simp_all

theorem tooth_sha3_256_category5_rejected (ctx digest : List UInt8) :
    encodePreHashMsgPrime slhDsaShake256f .sha3_256 ctx digest = none := by
  simp [encodePreHashMsgPrime, preHashCompatible, slhDsaShake256f, FipsPreHashAlg.securityBytes]

theorem witness_sha3_384_category3 :
    ∃ p alg ctx digest encoded,
      encodePreHashMsgPrime p alg ctx digest = some encoded := by
  refine ⟨slhDsaShake192f, .sha3_384, [], List.replicate 48 0, _, rfl⟩

#tooth_pair Qsag.accepted_preHash_category vs Qsag.tooth_sha3_256_category5_rejected
#verify_inhabited Qsag.accepted_preHash_category Qsag.witness_sha3_384_category3

end Qsag
end
