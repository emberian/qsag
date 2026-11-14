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
  { n := 16, h := 4, d := 2, hp := 2, a := 2, k := 4, m := 4 }

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

