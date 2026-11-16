module
public import Qsag.Math.Primality
public import Qsag.Math.Goldilocks
public import Qsag.Tactic.Prelude

public section
namespace Qsag
set_option autoImplicit false
set_option exponentiation.threshold 512
/-! ## 1. `SECP256K1_ORDER_N` & `ED25519_ORDER_L` Subgroup Semantics, Taproot Parity, Ed25519 Clamping & Shor Boundary -/

/-- Full-width 256-bit spending scalar / witness carrier. -/
abbrev MigrationKey256 := BitVec 256

/-- The `secp256k1` scalar modulus `SECP_N` (`secp256k1_ct.rs:19-24`). It is prime
    (`secp256k1OrderPrime_isPrime`); that it is the order of the generator on the curve is the
    hypothesis `Weierstrass.Secp256k1GroupLaws`, not a theorem of this file. -/
@[expose] def SECP256K1_ORDER_N : Nat :=
  0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141

/-- The `Ed25519` scalar modulus `ED_ORDER` (`scalar.rs:8-13`). This file uses it as a number;
    neither its primality nor its role as a subgroup order is proved here. -/
@[expose] def ED25519_ORDER_L : Nat :=
  0x1000000000000000000000000000000014DEF9DEA2F79CD65812631A5CF5D3ED

/-- Poseidon2 domain separator for canonical migration nullifiers (`scalar.rs:6`, `"MIG_NUL1"`). -/
def NULLIFIER_DOMAIN : UInt64 := 0x4d49475f4e554c31

/-- Little-endian 64-bit limb table for `SECP_N` matching `secp256k1_ct.rs:19-24`. -/
def secp256k1OrderLimbsLe : Fin 4 → UInt64
  | ⟨0, _⟩ => 0xBFD25E8CD0364141
  | ⟨1, _⟩ => 0xBAAEDCE6AF48A03B
  | ⟨2, _⟩ => 0xFFFFFFFFFFFFFFFE
  | ⟨3, _⟩ => 0xFFFFFFFFFFFFFFFF

/-- Little-endian 64-bit limb table for `ED_ORDER` matching `scalar.rs:8-13`. -/
def ed25519OrderLimbsLe : Fin 4 → UInt64
  | ⟨0, _⟩ => 0x5812631A5CF5D3ED
  | ⟨1, _⟩ => 0x14DEF9DEA2F79CD6
  | ⟨2, _⟩ => 0
  | ⟨3, _⟩ => 0x1000000000000000

/-- Reconstruct a 256-bit integer from 4 little-endian `UInt64` limbs (`scalar.rs:106-108`). -/
def limbs4LeToNat (limbs : Fin 4 → UInt64) : Nat :=
  (limbs ⟨0, by decide⟩).toNat +
  (limbs ⟨1, by decide⟩).toNat * (2 ^ 64) +
  (limbs ⟨2, by decide⟩).toNat * (2 ^ 128) +
  (limbs ⟨3, by decide⟩).toNat * (2 ^ 192)

/-- Legacy curve subgroup selector (`scalar.rs:22-33`). -/
inductive ScalarGroup where
  | Secp256k1
  | Ed25519
  deriving Repr, DecidableEq

/-- Exact subgroup order `group.order()` (`scalar.rs:27-32`). -/
@[expose] def ScalarGroup.orderNat : ScalarGroup → Nat
  | .Secp256k1 => SECP256K1_ORDER_N
  | .Ed25519   => ED25519_ORDER_L

/-- Subgroup domain separator limb `input[0]` inside `compute_nullifier` (`scalar.rs:93-96`). -/
def ScalarGroup.nullifierTag : ScalarGroup → Goldilocks
  | .Secp256k1 => ⟨1, by decide⟩
  | .Ed25519   => ⟨2, by decide⟩

/-- Circuit canonical scalar range guard `0 < s < group.orderNat` (`ownership.rs:261`, `scalar.rs:55-62`). -/
@[expose] def requireCanonicalScalar (group : ScalarGroup) (s : BitVec 256) : Bool :=
  (s.toNat != 0) && decide (s.toNat < group.orderNat)

theorem curve_orders_match_le_limbs_and_bounds :
    limbs4LeToNat secp256k1OrderLimbsLe = SECP256K1_ORDER_N ∧
    limbs4LeToNat ed25519OrderLimbsLe = ED25519_ORDER_L ∧
    2 ^ 255 < SECP256K1_ORDER_N ∧ SECP256K1_ORDER_N < 2 ^ 256 ∧ SECP256K1_ORDER_N % 2 = 1 ∧
    2 ^ 252 < ED25519_ORDER_L ∧ ED25519_ORDER_L < 2 ^ 253 ∧ ED25519_ORDER_L % 2 = 1 ∧
    ED25519_ORDER_L % 8 = 5 := by
  unfold limbs4LeToNat secp256k1OrderLimbsLe ed25519OrderLimbsLe SECP256K1_ORDER_N ED25519_ORDER_L
  decide

theorem scalarGroup_order_props (group : ScalarGroup) :
    1 < group.orderNat ∧ group.orderNat < 2 ^ 256 ∧ group.orderNat % 2 = 1 := by
  cases group <;> unfold ScalarGroup.orderNat SECP256K1_ORDER_N ED25519_ORDER_L <;> decide

theorem requireCanonicalScalar_iff (group : ScalarGroup) (s : BitVec 256) :
    requireCanonicalScalar group s = true ↔ (0 < s.toNat ∧ s.toNat < group.orderNat) := by
  unfold requireCanonicalScalar
  rw [Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq]
  constructor
  · rintro ⟨hNe, hLt⟩
    exact ⟨Nat.pos_of_ne_zero hNe, hLt⟩
  · rintro ⟨hPos, hLt⟩
    exact ⟨Nat.ne_of_gt hPos, hLt⟩

/-- Exact subgroup boundary behavior matching `scalar.rs:165-175` (`canonical_boundaries_and_wrap`):
    `0` and `group.orderNat` are rejected, whereas `group.orderNat - 1` is accepted. -/
theorem canonical_scalar_boundaries_exact (group : ScalarGroup) :
    requireCanonicalScalar group 0#256 = false ∧
    requireCanonicalScalar group (BitVec.ofNat 256 group.orderNat) = false ∧
    requireCanonicalScalar group (BitVec.ofNat 256 (group.orderNat - 1)) = true := by
  cases group <;>
    unfold requireCanonicalScalar ScalarGroup.orderNat SECP256K1_ORDER_N ED25519_ORDER_L <;>
    decide

/-- Negation `SECP_N - s` of a canonical `secp256k1` scalar (`legacy.rs:298, 318`). -/
def secpNegScalar (s : BitVec 256) : BitVec 256 :=
  if requireCanonicalScalar .Secp256k1 s then
    BitVec.ofNat 256 (SECP256K1_ORDER_N - s.toNat)
  else
    0#256

/-- Non-injective Bitcoin Taproot `x`-only equivalence (`legacy.rs:290-324`, `ownership.rs:281-284`):
    canonical nonzero scalars `s` and `SECP_N - s` share the identical curve `x`-coordinate. -/
@[expose] def taprootXOnlySameX (s1 s2 : BitVec 256) : Prop :=
  requireCanonicalScalar .Secp256k1 s1 = true ∧
  requireCanonicalScalar .Secp256k1 s2 = true ∧
  (s1 = s2 ∨ s2.toNat = SECP256K1_ORDER_N - s1.toNat)

private theorem cIte_pos {α : Type} {p : Prop} [inst : Decidable p] (hp : p) (a b : α) :
    (if p then a else b) = a := by
  cases inst with
  | isTrue _ => rfl
  | isFalse h => exact absurd hp h

private theorem cIte_neg {α : Type} {p : Prop} [inst : Decidable p] (hnp : ¬ p) (a b : α) :
    (if p then a else b) = b := by
  cases inst with
  | isTrue h => exact absurd h hnp
  | isFalse _ => rfl

private theorem cDIte_pos {α : Type} {p : Prop} [inst : Decidable p] (hp : p)
    (a : p → α) (b : ¬ p → α) : (if h : p then a h else b h) = a hp := by
  cases inst with
  | isTrue _ => rfl
  | isFalse h => exact absurd hp h

theorem secpNegScalar_props {s : BitVec 256}
    (hCanon : requireCanonicalScalar .Secp256k1 s = true) :
    (secpNegScalar s).toNat = SECP256K1_ORDER_N - s.toNat ∧
    requireCanonicalScalar .Secp256k1 (secpNegScalar s) = true ∧
    secpNegScalar (secpNegScalar s) = s ∧
    s ≠ secpNegScalar s ∧
    taprootXOnlySameX s (secpNegScalar s) := by
  have hb := curve_orders_match_le_limbs_and_bounds
  obtain ⟨hPos, hLtN⟩ := (requireCanonicalScalar_iff .Secp256k1 s).mp hCanon
  dsimp only [ScalarGroup.orderNat] at hLtN
  have hDiffLt256 : SECP256K1_ORDER_N - s.toNat < 2 ^ 256 := by omega
  have hNegToNat : (secpNegScalar s).toNat = SECP256K1_ORDER_N - s.toNat := by
    unfold secpNegScalar
    rw [hCanon]
    simp only [↓reduceIte, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hDiffLt256]
  have hNegCanon : requireCanonicalScalar .Secp256k1 (secpNegScalar s) = true := by
    rw [requireCanonicalScalar_iff, hNegToNat]
    dsimp only [ScalarGroup.orderNat]
    exact ⟨by omega, by omega⟩
  have hInv : secpNegScalar (secpNegScalar s) = s := by
    have hOuter : secpNegScalar (secpNegScalar s) =
        if requireCanonicalScalar .Secp256k1 (secpNegScalar s) then
          BitVec.ofNat 256 (SECP256K1_ORDER_N - (secpNegScalar s).toNat)
        else 0#256 := rfl
    rw [hOuter, hNegCanon]
    simp only [↓reduceIte, hNegToNat]
    apply BitVec.eq_of_toNat_eq
    have hsLt256 : s.toNat < 2 ^ 256 := s.isLt
    have hSubSub : SECP256K1_ORDER_N - (SECP256K1_ORDER_N - s.toNat) = s.toNat := by omega
    rw [BitVec.toNat_ofNat, hSubSub, Nat.mod_eq_of_lt hsLt256]
  have hNe : s ≠ secpNegScalar s := by
    intro hEq
    have hv := congrArg BitVec.toNat hEq
    rw [hNegToNat] at hv
    have hOdd : SECP256K1_ORDER_N % 2 = 1 := hb.2.2.2.2.1
    omega
  exact ⟨hNegToNat, hNegCanon, hInv, hNe, ⟨hCanon, hNegCanon, Or.inr hNegToNat⟩⟩

/-- `x`-only & `y`-parity projection of the multiples `[s]G`, `0 < s < n`, of a generator of
    order `n` (BIP-340 x-only public keys; `ownership.rs:281-284`): `[s]G` and `[n - s]G` are
    the only multiples sharing an `x`-coordinate (`sameX_iff`), and their `y` parities are
    opposite (`yParity_neg`). The interface does not say where `xOf`/`yParity` come from.
    `Weierstrass.Curve.PrimeOrderGroup.projection` builds it from the affine coordinates of
    curve points; `scalarModelTaprootProjection` builds it from scalars alone. -/
structure TaprootCurveProjection (n : Nat) (XCoord : Type) where
  xOf         : Nat → XCoord
  yParity     : Nat → Bool
  sameX_iff   : ∀ s1 s2, 0 < s1 → s1 < n → 0 < s2 → s2 < n →
    (xOf s1 = xOf s2 ↔ (s1 = s2 ∨ s2 = n - s1))
  yParity_neg : ∀ s, 0 < s → s < n → yParity (n - s) = !(yParity s)

/-- Scalar-level model of the interface at any odd order: `xOf s = min(s, n - s)` and
    `yParity s = (n < 2s)`. It contains no curve. Its only use is to show that the two
    interface laws are jointly consistent at every odd `n`, `SECP256K1_ORDER_N` included;
    the curve-point instance is `Weierstrass.Curve.PrimeOrderGroup.projection`. -/
def scalarModelTaprootProjection (n : Nat) (hOdd : n % 2 = 1) : TaprootCurveProjection n Nat where
  xOf s := if s ≤ n - s then s else n - s
  yParity s := decide (n < 2 * s)
  sameX_iff s1 s2 _ l1 _ l2 := by
    by_cases a : s1 ≤ n - s1 <;> by_cases c : s2 ≤ n - s2 <;>
      simp only [a, c, ↓reduceIte] <;>
      (constructor
       · intro h
         by_cases e : s1 = s2
         · exact .inl e
         · exact .inr (by omega)
       · intro h
         rcases h with h | h <;> omega)
  yParity_neg s _ l := by
    by_cases h : n < 2 * s
    · rw [decide_eq_true h, decide_eq_false (by omega : ¬ n < 2 * (n - s))]
      rfl
    · rw [decide_eq_false h, decide_eq_true (by omega : n < 2 * (n - s))]
      rfl

/-- The compressed `(x, y-parity)` encoding is injective on `[1, n)` (SEC 1 §2.3.3 point
    compression; `BitcoinHash160` at `ownership.rs:265-267`). -/
theorem TaprootCurveProjection.compressed_injective {n : Nat} {XCoord : Type}
    (proj : TaprootCurveProjection n XCoord) :
    (∀ s1 s2, 0 < s1 → s1 < n → 0 < s2 → s2 < n →
      proj.xOf s1 = proj.xOf s2 → proj.yParity s1 = proj.yParity s2 → s1 = s2) ∧
    (∀ s, 0 < s → s < n → proj.xOf (n - s) = proj.xOf s) := by
  refine ⟨?_, fun s p l => ((proj.sameX_iff s (n - s) p l (by omega) (by omega)).mpr (Or.inr rfl)).symm⟩
  intro s1 s2 p1 l1 p2 l2 hX hY
  rcases (proj.sameX_iff s1 s2 p1 l1 p2 l2).mp hX with h | h
  · exact h
  · subst h
    rw [proj.yParity_neg s1 p1 l1] at hY
    cases hb : proj.yParity s1 <;> rw [hb] at hY <;> cases hY

private theorem TaprootCurveProjection.sameX_iff_canonical {XCoord : Type}
    (proj : TaprootCurveProjection SECP256K1_ORDER_N XCoord) (s1 s2 : BitVec 256)
    (h1 : requireCanonicalScalar .Secp256k1 s1 = true)
    (h2 : requireCanonicalScalar .Secp256k1 s2 = true) :
    proj.xOf s1.toNat = proj.xOf s2.toNat ↔ taprootXOnlySameX s1 s2 := by
  obtain ⟨p1, l1⟩ := (requireCanonicalScalar_iff .Secp256k1 s1).mp h1
  obtain ⟨p2, l2⟩ := (requireCanonicalScalar_iff .Secp256k1 s2).mp h2
  rw [proj.sameX_iff _ _ p1 l1 p2 l2]
  constructor
  · rintro (h | h)
    · exact ⟨h1, h2, Or.inl (BitVec.eq_of_toNat_eq h)⟩
    · exact ⟨h1, h2, Or.inr h⟩
  · rintro ⟨_, _, h | h⟩
    · exact Or.inl (congrArg BitVec.toNat h)
    · exact Or.inr h

private theorem TaprootCurveProjection.yParity_neg_canonical {XCoord : Type}
    (proj : TaprootCurveProjection SECP256K1_ORDER_N XCoord) (s : BitVec 256)
    (h : requireCanonicalScalar .Secp256k1 s = true) :
    proj.yParity (secpNegScalar s).toNat = !(proj.yParity s.toNat) := by
  obtain ⟨p, l⟩ := (requireCanonicalScalar_iff .Secp256k1 s).mp h
  rw [(secpNegScalar_props h).1]
  exact proj.yParity_neg _ p l

/-- Normalize any canonical `secp256k1` scalar to its even-`y` Taproot representative (`legacy.rs:299-301, 319-321`). -/
def normalizeTaprootEvenY {XCoord : Type} (proj : TaprootCurveProjection SECP256K1_ORDER_N XCoord)
    (s : BitVec 256) : BitVec 256 :=
  if proj.yParity s.toNat then secpNegScalar s else s

/-- **Taproot Even-`y` Parity Constraint Restores Canonical Injectivity**, for any projection
    at the `secp256k1` order (in particular `secp256k1TaprootProjection`, whose `xOf` and
    `yParity` are affine coordinates of `[s]G`):
    1. Enforcing `proj.yParity s = false` (`c.output(y[0])` at `ownership.rs:282`) makes `proj.xOf`
       injective across all canonical `secp256k1` scalars.
    2. Compressed `(proj.xOf s, proj.yParity s)` (`BitcoinHash160` at `ownership.rs:265-267`) is
       injective across all canonical scalars `1 ≤ s < SECP_N`.
    3. `normalizeTaprootEvenY` produces a canonical scalar sharing the same `x`-coordinate with
       even `y[0]` parity (`false`). -/
theorem taproot_even_y_parity_restores_canonical_injectivity
    {XCoord : Type} (proj : TaprootCurveProjection SECP256K1_ORDER_N XCoord) :
    (∀ s1 s2 : BitVec 256,
      requireCanonicalScalar .Secp256k1 s1 = true →
      requireCanonicalScalar .Secp256k1 s2 = true →
      proj.yParity s1.toNat = false →
      proj.yParity s2.toNat = false →
      proj.xOf s1.toNat = proj.xOf s2.toNat →
      s1 = s2) ∧
    (∀ s1 s2 : BitVec 256,
      requireCanonicalScalar .Secp256k1 s1 = true →
      requireCanonicalScalar .Secp256k1 s2 = true →
      proj.xOf s1.toNat = proj.xOf s2.toNat →
      proj.yParity s1.toNat = proj.yParity s2.toNat →
      s1 = s2) ∧
    (∀ s : BitVec 256,
      requireCanonicalScalar .Secp256k1 s = true →
      requireCanonicalScalar .Secp256k1 (normalizeTaprootEvenY proj s) = true ∧
      proj.xOf (normalizeTaprootEvenY proj s).toNat = proj.xOf s.toNat ∧
      proj.yParity (normalizeTaprootEvenY proj s).toNat = false) := by
  have hPairInj : ∀ s1 s2 : BitVec 256,
      requireCanonicalScalar .Secp256k1 s1 = true →
      requireCanonicalScalar .Secp256k1 s2 = true →
      proj.xOf s1.toNat = proj.xOf s2.toNat →
      proj.yParity s1.toNat = proj.yParity s2.toNat →
      s1 = s2 := by
    intro s1 s2 h1 h2 hX hY
    obtain ⟨p1, l1⟩ := (requireCanonicalScalar_iff .Secp256k1 s1).mp h1
    obtain ⟨p2, l2⟩ := (requireCanonicalScalar_iff .Secp256k1 s2).mp h2
    exact BitVec.eq_of_toNat_eq (proj.compressed_injective.1 _ _ p1 l1 p2 l2 hX hY)
  refine ⟨fun s1 s2 h1 h2 hy1 hy2 hX => hPairInj s1 s2 h1 h2 hX (hy1.trans hy2.symm), hPairInj, ?_⟩
  intro s hCanon
  unfold normalizeTaprootEvenY
  cases hy : proj.yParity s.toNat
  · change requireCanonicalScalar .Secp256k1 s = true ∧
      proj.xOf s.toNat = proj.xOf s.toNat ∧ proj.yParity s.toNat = false
    exact ⟨hCanon, rfl, hy⟩
  · change requireCanonicalScalar .Secp256k1 (secpNegScalar s) = true ∧
      proj.xOf (secpNegScalar s).toNat = proj.xOf s.toNat ∧
      proj.yParity (secpNegScalar s).toNat = false
    obtain ⟨_, hNegCanon, _, _, hSame⟩ := secpNegScalar_props hCanon
    have hXEq : proj.xOf s.toNat = proj.xOf (secpNegScalar s).toNat :=
      (proj.sameX_iff_canonical s (secpNegScalar s) hCanon hNegCanon).mpr hSame
    have hNegPar := proj.yParity_neg_canonical s hCanon
    rw [hy] at hNegPar
    exact ⟨hNegCanon, hXEq.symm, hNegPar⟩

/-! ### Short-Weierstrass affine arithmetic over `ℤ/p` and the curve-point projection

Affine chord-tangent arithmetic on `y² = x³ + a·x + b` over the residues mod `p`
(Silverman, *The Arithmetic of Elliptic Curves*, III.2.3; SEC 1 v2.0 §2.2.1), with
the point at infinity as `none`. What is proved for every curve and every odd prime
`p`: negation stays on the curve and keeps `x`; `y` and `p - y` have opposite parity
when `0 < y < p`; two curve points with one `x` are equal or negatives; and
`P + Q = O` exactly when `Q = -P`. Associativity and closure of the addition are not
proved in general. A generator's group facts are collected in `PrimeOrderGroup`,
which is proved outright for `y² = x³ + 7` over `ℤ/43` (`secp7Mod43_group`) and is
a named hypothesis for `secp256k1` (`Secp256k1GroupLaws`). -/

namespace Weierstrass


private theorem mod_zero_cases {p z : Nat} (hz : z < 2 * p) (h : z % p = 0) : z = 0 ∨ z = p := by
  by_cases hlt : z < p
  · rw [Nat.mod_eq_of_lt hlt] at h
    exact Or.inl h
  · have hge : p ≤ z := Nat.le_of_not_lt hlt
    rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)] at h
    exact Or.inr (by omega)

/-- `(p - y)² ≡ y² (mod p)`. -/
private theorem neg_sq_mod {p y : Nat} (hy : y < p) :
    ((p - y) % p * ((p - y) % p)) % p = (y * y) % p := by
  by_cases h0 : y = 0
  · subst h0
    rw [Nat.sub_zero, Nat.mod_self]
  · obtain ⟨d, rfl⟩ : ∃ d, p = d + y := ⟨p - y, by omega⟩
    rw [Nat.add_sub_cancel, Nat.mod_eq_of_lt (by omega : d < d + y)]
    have hId : d * d + y * (d + y) = (d + y) * d + y * y := by
      rw [Nat.mul_add, Nat.add_mul]
      omega
    calc (d * d) % (d + y) = (d * d + y * (d + y)) % (d + y) :=
          (Nat.add_mul_mod_self_right _ _ _).symm
      _ = ((d + y) * d + y * y) % (d + y) := by rw [hId]
      _ = (y * y) % (d + y) := Nat.mul_add_mod_self_left _ _ _

/-- In `ℤ/p` with `p` prime, `u² = v²` forces `v = u` or `v = -u`. -/
private theorem sq_mod_eq_cases {p u v : Nat} (hp : IsPrime p) (huv : u ≤ v) (hv : v < p)
    (h : (u * u) % p = (v * v) % p) : v = u ∨ u + v = p := by
  have hDvd : p ∣ (v + u) * (v - u) := by
    rw [← Nat.mul_self_sub_mul_self_eq]
    exact Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq h.symm)
  rcases hp.dvd_mul hDvd with hs | hd
  · rcases mod_zero_cases (by omega : v + u < 2 * p) (Nat.mod_eq_zero_of_dvd hs) with h0 | hpEq
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  · exact Or.inl (by
      have := Nat.eq_zero_of_dvd_of_lt hd (by omega : v - u < p)
      omega)

/-- A short-Weierstrass curve `y² = x³ + a·x + b` over the residues mod `p`. -/
structure Curve where
  p : Nat
  a : Nat
  b : Nat

/-- Affine points with reduced coordinates; `none` is the point at infinity. -/
abbrev Point := Option (Nat × Nat)

/-- The affine `x`-coordinate; the point at infinity has none. -/
def Point.x : Point → Option Nat
  | none => none
  | some (x, _) => some x

/-- The least significant bit of the affine `y`-coordinate (`y[0]` at `ownership.rs:282`). -/
def Point.yOdd : Point → Bool
  | none => false
  | some (_, y) => y % 2 == 1

/-- Reduced coordinates satisfying the curve equation. -/
def Curve.OnCurve (C : Curve) : Point → Prop
  | none => True
  | some (x, y) => x < C.p ∧ y < C.p ∧ (y * y) % C.p = (x * x * x + C.a * x + C.b) % C.p

private instance Curve.decOnCurve (C : Curve) : (P : Point) → Decidable (C.OnCurve P)
  | none => isTrue trivial
  | some (x, y) => inferInstanceAs (Decidable
      (x < C.p ∧ y < C.p ∧ (y * y) % C.p = (x * x * x + C.a * x + C.b) % C.p))

/-- `-(x, y) = (x, -y)`. -/
def Curve.neg (C : Curve) : Point → Point
  | none => none
  | some (x, y) => some (x, (C.p - y) % C.p)

/-- Field inverse by Fermat's little theorem, `z⁻¹ = z^(p-2)`. -/
def Curve.inv (C : Curve) (z : Nat) : Nat := z ^ (C.p - 2) % C.p

/-- Chord-tangent addition (Silverman III.2.3): `λ = (y₂ - y₁)/(x₂ - x₁)` on a chord,
    `λ = (3x₁² + a)/(2y₁)` on a tangent, `x₃ = λ² - x₁ - x₂`, `y₃ = λ(x₁ - x₃) - y₁`. -/
def Curve.add (C : Curve) : Point → Point → Point
  | none, Q => Q
  | some P, none => some P
  | some (x1, y1), some (x2, y2) =>
    if x1 = x2 ∧ (y1 + y2) % C.p = 0 then none
    else
      let lam :=
        if x1 = x2 then ((3 * x1 * x1 + C.a) * C.inv (2 * y1)) % C.p
        else (((y2 + C.p - y1) % C.p) * C.inv ((x2 + C.p - x1) % C.p)) % C.p
      let x3 := (lam * lam + (C.p - x1) + (C.p - x2)) % C.p
      some (x3, (lam * ((x1 + C.p - x3) % C.p) + (C.p - y1)) % C.p)

/-- `[k]P` by repeated addition. -/
def Curve.smul (C : Curve) : Nat → Point → Point
  | 0, _ => none
  | k + 1, P => C.add (C.smul k P) P

theorem Curve.neg_x (C : Curve) (P : Point) : Point.x (C.neg P) = Point.x P := by
  match P with
  | none => rfl
  | some (_, _) => rfl

/-- Negation maps the curve to itself. -/
theorem Curve.neg_onCurve (C : Curve) (P : Point) (h : C.OnCurve P) : C.OnCurve (C.neg P) := by
  match P, h with
  | none, _ => trivial
  | some (x, y), ⟨hx, hy, hEq⟩ =>
    exact ⟨hx, Nat.mod_lt _ (by omega), (neg_sq_mod hy).trans hEq⟩

/-- Over an odd modulus a nonzero `y` and its negative `p - y` have opposite parity. -/
theorem neg_y_parity {p y : Nat} (hp : p % 2 = 1) (h0 : 0 < y) (hy : y < p) :
    ((p - y) % p % 2 == 1) = !(y % 2 == 1) := by
  rw [Nat.mod_eq_of_lt (by omega : p - y < p)]
  rcases Nat.mod_two_eq_zero_or_one y with h | h
  · rw [h, (by omega : (p - y) % 2 = 1)]
    rfl
  · rw [h, (by omega : (p - y) % 2 = 0)]
    rfl

/-- Two affine curve points with one `x`-coordinate are equal or negatives of each other.
    This is where primality of `p` enters. -/
theorem Curve.eq_or_eq_neg_of_same_x (C : Curve) (hp : IsPrime C.p) {x y1 y2 : Nat}
    (h1 : C.OnCurve (some (x, y1))) (h2 : C.OnCurve (some (x, y2))) :
    (some (x, y2) : Point) = some (x, y1) ∨ (some (x, y2) : Point) = C.neg (some (x, y1)) := by
  obtain ⟨_, hy1, e1⟩ := h1
  obtain ⟨_, hy2, e2⟩ := h2
  have hsq : (y1 * y1) % C.p = (y2 * y2) % C.p := e1.trans e2.symm
  have hNeg : y1 + y2 = C.p → (some (x, y2) : Point) = C.neg (some (x, y1)) := by
    intro hs
    show (some (x, y2) : Point) = some (x, (C.p - y1) % C.p)
    rw [Nat.mod_eq_of_lt (by omega : C.p - y1 < C.p), (by omega : C.p - y1 = y2)]
  rcases Nat.le_total y1 y2 with hle | hle
  · rcases sq_mod_eq_cases hp hle hy2 hsq with h | h
    · exact Or.inl (by rw [h])
    · exact Or.inr (hNeg h)
  · rcases sq_mod_eq_cases hp hle hy1 hsq.symm with h | h
    · exact Or.inl (by rw [h])
    · exact Or.inr (hNeg (by omega))

/-- `P + Q = O` exactly when `Q = -P`, for affine curve points. -/
theorem Curve.add_eq_none_iff_neg (C : Curve) {P Q : Nat × Nat}
    (hP : C.OnCurve (some P)) (hQ : C.OnCurve (some Q)) :
    C.add (some P) (some Q) = none ↔ (some Q : Point) = C.neg (some P) := by
  obtain ⟨x1, y1⟩ := P
  obtain ⟨x2, y2⟩ := Q
  obtain ⟨_, hy1, _⟩ := hP
  obtain ⟨_, hy2, _⟩ := hQ
  have hY : (y1 + y2) % C.p = 0 ↔ y2 = (C.p - y1) % C.p := by
    constructor
    · intro h
      rcases mod_zero_cases (by omega : y1 + y2 < 2 * C.p) h with h0 | hpEq
      · rw [(by omega : y1 = 0), (by omega : y2 = 0), Nat.sub_zero, Nat.mod_self]
      · rw [Nat.mod_eq_of_lt (by omega : C.p - y1 < C.p)]
        omega
    · intro h
      by_cases h0 : y1 = 0
      · subst h0
        rw [Nat.sub_zero, Nat.mod_self] at h
        subst h
        exact Nat.zero_mod _
      · rw [Nat.mod_eq_of_lt (by omega : C.p - y1 < C.p)] at h
        rw [(by omega : y1 + y2 = C.p), Nat.mod_self]
  show (if x1 = x2 ∧ (y1 + y2) % C.p = 0 then none else _) = none ↔
    (some (x2, y2) : Point) = some (x1, (C.p - y1) % C.p)
  by_cases hc : x1 = x2 ∧ (y1 + y2) % C.p = 0
  · rw [cIte_pos hc]
    obtain ⟨hx, hy⟩ := hc
    exact ⟨fun _ => by rw [hx, hY.mp hy], fun _ => rfl⟩
  · rw [cIte_neg hc]
    refine ⟨fun h => (by cases h), fun h => absurd ?_ hc⟩
    have hx : x2 = x1 := congrArg Prod.fst (Option.some.inj h)
    have hy : y2 = (C.p - y1) % C.p := congrArg Prod.snd (Option.some.inj h)
    exact ⟨hx.symm, hY.mpr hy⟩

/-- The facts about a generator `G` that make `s ↦ [s]G` a faithful copy of `ℤ/n` on the
    curve, with `p` an odd prime and `n` an odd prime. `smul_add` is the homomorphism law of the
    cyclic subgroup; with `order` and `exact` it gives `[n - s]G = -[s]G` and injectivity on
    `[0, n)`. None of the four group fields (`onCurve`, `smul_add`, `order`, `exact`) is derived
    here from the addition formulas. -/
structure Curve.PrimeOrderGroup (C : Curve) (G : Point) (n : Nat) : Prop where
  p_prime  : IsPrime C.p
  p_odd    : C.p % 2 = 1
  n_prime  : IsPrime n
  n_odd    : n % 2 = 1
  onCurve  : ∀ k, C.OnCurve (C.smul k G)
  smul_add : ∀ a b, C.smul (a + b) G = C.add (C.smul a G) (C.smul b G)
  order    : C.smul n G = none
  exact    : ∀ k, 0 < k → k < n → C.smul k G ≠ none

namespace Curve.PrimeOrderGroup

variable {C : Curve} {G : Point} {n : Nat}

/-- `[n - s]G = -[s]G`. -/
theorem smul_neg (h : C.PrimeOrderGroup G n) {s : Nat} (h0 : 0 < s) (hs : s < n) :
    C.smul (n - s) G = C.neg (C.smul s G) := by
  have hSum : C.add (C.smul s G) (C.smul (n - s) G) = none := by
    rw [← h.smul_add, (by omega : s + (n - s) = n), h.order]
  have hP := h.onCurve s
  have hQ := h.onCurve (n - s)
  cases hPe : C.smul s G with
  | none => exact absurd hPe (h.exact s h0 hs)
  | some P =>
    cases hQe : C.smul (n - s) G with
    | none => exact absurd hQe (h.exact (n - s) (by omega) (by omega))
    | some Q =>
      rw [hPe] at hP hSum
      rw [hQe] at hQ hSum
      exact (C.add_eq_none_iff_neg hP hQ).mp hSum

private theorem smul_ne_of_lt (h : C.PrimeOrderGroup G n) {a b : Nat} (hab : a < b) (hb : b < n) :
    C.smul a G ≠ C.smul b G := by
  intro hEq
  have h1 : C.smul (n - a + b) G = none := by
    rw [h.smul_add, ← hEq, ← h.smul_add, (by omega : n - a + a = n), h.order]
  have h2 : C.smul (n - a + b) G = C.smul (b - a) G := by
    rw [(by omega : n - a + b = n + (b - a)), h.smul_add, h.order]
    rfl
  exact h.exact (b - a) (by omega) (by omega) (h2.symm.trans h1)

/-- `s ↦ [s]G` is injective on `[0, n)`. -/
theorem smul_injective (h : C.PrimeOrderGroup G n) {a b : Nat} (ha : a < n) (hb : b < n)
    (hEq : C.smul a G = C.smul b G) : a = b := by
  rcases Nat.lt_trichotomy a b with hlt | heq | hgt
  · exact absurd hEq (h.smul_ne_of_lt hlt hb)
  · exact heq
  · exact absurd hEq.symm (h.smul_ne_of_lt hgt ha)

/-- No multiple `[s]G`, `0 < s < n`, has `y = 0`: such a point is its own negative, and
    `[n - s]G = [s]G` contradicts injectivity because `n` is odd. -/
theorem smul_y_ne_zero (h : C.PrimeOrderGroup G n) {s x y : Nat} (h0 : 0 < s) (hs : s < n)
    (hP : C.smul s G = some (x, y)) : y ≠ 0 := by
  intro hy
  subst hy
  have hNeg := h.smul_neg h0 hs
  rw [hP] at hNeg
  have hSelf : C.neg (some (x, 0)) = some (x, 0) := by
    show (some (x, (C.p - 0) % C.p) : Point) = some (x, 0)
    rw [Nat.sub_zero, Nat.mod_self]
  rw [hSelf, ← hP] at hNeg
  have := h.smul_injective (by omega) hs hNeg
  have := h.n_odd
  omega

/-- **Curve-point x-only and parity laws.** For a generator `G` of odd order `n` on a
    short-Weierstrass curve over an odd prime field:
    1. `[s₁]G` and `[s₂]G` (`0 < sᵢ < n`) have one affine `x`-coordinate exactly when
       `s₂ = s₁` or `s₂ = n - s₁`;
    2. `[n - s]G = -[s]G`, and the least significant bits of the two affine
       `y`-coordinates differ. -/
theorem xonly_parity_laws (h : C.PrimeOrderGroup G n) :
    (∀ s1 s2, 0 < s1 → s1 < n → 0 < s2 → s2 < n →
      (Point.x (C.smul s1 G) = Point.x (C.smul s2 G) ↔ (s1 = s2 ∨ s2 = n - s1))) ∧
    (∀ s, 0 < s → s < n →
      C.smul (n - s) G = C.neg (C.smul s G) ∧
      Point.yOdd (C.smul (n - s) G) = !(Point.yOdd (C.smul s G))) := by
  constructor
  · intro s1 s2 p1 l1 p2 l2
    constructor
    · intro hx
      have hC1 := h.onCurve s1
      have hC2 := h.onCurve s2
      have hNeg := h.smul_neg p1 l1
      cases hP : C.smul s1 G with
      | none => exact absurd hP (h.exact s1 p1 l1)
      | some P =>
        cases hQ : C.smul s2 G with
        | none => exact absurd hQ (h.exact s2 p2 l2)
        | some Q =>
          obtain ⟨x1, y1⟩ := P
          obtain ⟨x2, y2⟩ := Q
          rw [hP, hQ] at hx
          have hxe : x1 = x2 := Option.some.inj hx
          subst hxe
          rw [hP] at hC1 hNeg
          rw [hQ] at hC2
          rcases C.eq_or_eq_neg_of_same_x h.p_prime hC1 hC2 with hEq | hEq
          · exact Or.inl (h.smul_injective l1 l2 (hP.trans (hEq.symm.trans hQ.symm)))
          · exact Or.inr (h.smul_injective l2 (by omega) (hQ.trans (hEq.trans hNeg.symm)))
    · rintro (hEq | hEq)
      · rw [hEq]
      · rw [hEq, h.smul_neg p1 l1, C.neg_x]
  · intro s p l
    have hNeg := h.smul_neg p l
    refine ⟨hNeg, ?_⟩
    have hC := h.onCurve s
    cases hP : C.smul s G with
    | none => exact absurd hP (h.exact s p l)
    | some P =>
      obtain ⟨x, y⟩ := P
      rw [hP] at hC
      rw [hNeg, hP]
      exact neg_y_parity h.p_odd (Nat.pos_of_ne_zero (h.smul_y_ne_zero p l hP)) hC.2.1

/-- The projection whose `xOf` and `yParity` are the affine `x`-coordinate and the
    `y`-coordinate's least significant bit of the curve point `[s]G`. -/
def projection (h : C.PrimeOrderGroup G n) : TaprootCurveProjection n (Option Nat) where
  xOf s := Point.x (C.smul s G)
  yParity s := Point.yOdd (C.smul s G)
  sameX_iff := h.xonly_parity_laws.1
  yParity_neg s p l := (h.xonly_parity_laws.2 s p l).2

end Curve.PrimeOrderGroup

/-! #### A complete instance: `y² = x³ + 7` over `ℤ/43`, generator `(2, 12)`, order `31`

The same equation as `secp256k1` (`a = 0`, `b = 7`, `p ≡ 3 mod 4`, `p ≡ 1 mod 3`) over a
field small enough for the kernel to check the whole group table. -/

def secp7Mod43 : Curve := ⟨43, 0, 7⟩

def secp7Mod43G : Point := some (2, 12)

private theorem prime43 : IsPrime 43 := by
  refine ⟨by decide, fun d hd => ?_⟩
  have key : ∀ d, d < 44 → d ∣ 43 → d = 1 ∨ d = 43 := by decide
  exact key d (Nat.lt_succ_of_le (Nat.le_of_dvd (by decide) hd)) hd

private theorem prime31 : IsPrime 31 := by
  refine ⟨by decide, fun d hd => ?_⟩
  have key : ∀ d, d < 32 → d ∣ 31 → d = 1 ∨ d = 31 := by decide
  exact key d (Nat.lt_succ_of_le (Nat.le_of_dvd (by decide) hd)) hd

private theorem secp7Mod43_table :
    ∀ i, i < 31 → ∀ j, j < 31 →
      secp7Mod43.add (secp7Mod43.smul i secp7Mod43G) (secp7Mod43.smul j secp7Mod43G) =
        secp7Mod43.smul ((i + j) % 31) secp7Mod43G := by
  decide +kernel

private theorem secp7Mod43_periodic : ∀ k,
    secp7Mod43.smul k secp7Mod43G = secp7Mod43.smul (k % 31) secp7Mod43G := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    have hStep := secp7Mod43_table (k % 31) (Nat.mod_lt _ (by decide)) 1 (by decide)
    have hOne : secp7Mod43.smul 1 secp7Mod43G = secp7Mod43G := rfl
    rw [hOne] at hStep
    show secp7Mod43.add (secp7Mod43.smul k secp7Mod43G) secp7Mod43G = _
    rw [ih, hStep, (by omega : (k % 31 + 1) % 31 = (k + 1) % 31)]

/-- The generator `(2, 12)` of `y² = x³ + 7` over `ℤ/43` has exact prime order `31`, and
    all eight `PrimeOrderGroup` facts hold; the group table is checked by the kernel. -/
theorem secp7Mod43_group : secp7Mod43.PrimeOrderGroup secp7Mod43G 31 where
  p_prime := prime43
  p_odd := by decide
  n_prime := prime31
  n_odd := by decide
  onCurve k := by
    have key : ∀ i, i < 31 → secp7Mod43.OnCurve (secp7Mod43.smul i secp7Mod43G) := by
      decide +kernel
    rw [secp7Mod43_periodic]
    exact key _ (Nat.mod_lt _ (by decide))
  smul_add a b := by
    calc secp7Mod43.smul (a + b) secp7Mod43G
        = secp7Mod43.smul ((a + b) % 31) secp7Mod43G := secp7Mod43_periodic _
      _ = secp7Mod43.smul ((a % 31 + b % 31) % 31) secp7Mod43G := by
          rw [(by omega : (a + b) % 31 = (a % 31 + b % 31) % 31)]
      _ = secp7Mod43.add (secp7Mod43.smul (a % 31) secp7Mod43G)
            (secp7Mod43.smul (b % 31) secp7Mod43G) :=
          (secp7Mod43_table _ (Nat.mod_lt _ (by decide)) _ (Nat.mod_lt _ (by decide))).symm
      _ = secp7Mod43.add (secp7Mod43.smul a secp7Mod43G) (secp7Mod43.smul b secp7Mod43G) := by
          rw [← secp7Mod43_periodic a, ← secp7Mod43_periodic b]
  order := by decide +kernel
  exact k h0 hk := by
    have key : ∀ i, i < 31 → 0 < i → secp7Mod43.smul i secp7Mod43G ≠ none := by
      decide +kernel
    exact key k hk h0

theorem inhabited_prime_order_curve_group :
    ∃ (C : Curve) (G : Point) (n : Nat), C.PrimeOrderGroup G n :=
  ⟨secp7Mod43, secp7Mod43G, 31, secp7Mod43_group⟩

#verify_inhabited
  Qsag.Weierstrass.Curve.PrimeOrderGroup.xonly_parity_laws
  Qsag.Weierstrass.inhabited_prime_order_curve_group

/-- The curve-point projection on `y² = x³ + 7` over `ℤ/43`. -/
def secp7Mod43Projection : TaprootCurveProjection 31 (Option Nat) :=
  secp7Mod43_group.projection

/-- Concrete coordinates behind the projection: `[1]G = (2, 12)` and `[30]G = (2, 31)`
    share `x = 2` with opposite parity, `[2]G = (7, 7)` has another `x`, and the
    compressed encoding separates all thirty nonzero multiples. -/
theorem secp7Mod43_projection_coordinates :
    secp7Mod43.smul 1 secp7Mod43G = some (2, 12) ∧
    secp7Mod43.smul 30 secp7Mod43G = some (2, 31) ∧
    secp7Mod43.smul 2 secp7Mod43G = some (7, 7) ∧
    secp7Mod43Projection.xOf 1 = secp7Mod43Projection.xOf 30 ∧
    secp7Mod43Projection.yParity 1 = false ∧
    secp7Mod43Projection.yParity 30 = true ∧
    (∀ s1 s2, 0 < s1 → s1 < 31 → 0 < s2 → s2 < 31 →
      secp7Mod43Projection.xOf s1 = secp7Mod43Projection.xOf s2 →
      secp7Mod43Projection.yParity s1 = secp7Mod43Projection.yParity s2 → s1 = s2) :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, secp7Mod43Projection.compressed_injective.1⟩

/-! #### `secp256k1`

Checked by the kernel: the field prime and generator limbs of `secp256k1_ct.rs:8-40`,
`p` and `n` odd, `p ≡ 3 (mod 4)`, `a = 0`, `b = 7`, and `G` on the curve. Primality of
`p` and of `n` is proved by Pocklington certificates (`secp256k1FieldPrime_isPrime`,
`secp256k1OrderPrime_isPrime`). Not proved: the four group facts of `PrimeOrderGroup` for
`G` (closure of its multiples, the homomorphism law, `[n]G = O`, exact order). They are
what `Secp256k1GroupLaws` adds to the proved fields (`secp256k1GroupLaws_of_group_facts`);
SEC 2 v2.0 §2.4.1 states them for these parameters. -/

/-- `secp256k1` field prime `p = 2^256 - 2^32 - 977` (`secp256k1_ct.rs:8-13`). -/
def SECP256K1_FIELD_P : Nat :=
  0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F

def secp256k1FieldLimbsLe : Fin 4 → UInt64
  | ⟨0, _⟩ => 0xFFFFFFFEFFFFFC2F
  | ⟨1, _⟩ => 0xFFFFFFFFFFFFFFFF
  | ⟨2, _⟩ => 0xFFFFFFFFFFFFFFFF
  | ⟨3, _⟩ => 0xFFFFFFFFFFFFFFFF

/-- `SECP_GX` (`secp256k1_ct.rs:27-32`). -/
def secp256k1GxLimbsLe : Fin 4 → UInt64
  | ⟨0, _⟩ => 0x59F2815B16F81798
  | ⟨1, _⟩ => 0x029BFCDB2DCE28D9
  | ⟨2, _⟩ => 0x55A06295CE870B07
  | ⟨3, _⟩ => 0x79BE667EF9DCBBAC

/-- `SECP_GY` (`secp256k1_ct.rs:35-40`). -/
def secp256k1GyLimbsLe : Fin 4 → UInt64
  | ⟨0, _⟩ => 0x9C47D08FFB10D4B8
  | ⟨1, _⟩ => 0xFD17B448A6855419
  | ⟨2, _⟩ => 0x5DA4FBFC0E1108A8
  | ⟨3, _⟩ => 0x483ADA7726A3C465

/-- `y² = x³ + 7` over `ℤ/p` (`secp256k1_ct.rs:1-2`). -/
def secp256k1Curve : Curve := ⟨SECP256K1_FIELD_P, 0, 7⟩

/-- The standard generator (SEC 2 v2.0 §2.4.1). -/
def secp256k1G : Point :=
  some (0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798,
        0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8)

theorem secp256k1_checked_parameters :
    SECP256K1_FIELD_P = 2 ^ 256 - 2 ^ 32 - 977 ∧
    limbs4LeToNat secp256k1FieldLimbsLe = SECP256K1_FIELD_P ∧
    secp256k1G = some (limbs4LeToNat secp256k1GxLimbsLe, limbs4LeToNat secp256k1GyLimbsLe) ∧
    secp256k1Curve.p % 2 = 1 ∧ secp256k1Curve.p % 4 = 3 ∧
    secp256k1Curve.a = 0 ∧ secp256k1Curve.b = 7 ∧
    SECP256K1_ORDER_N % 2 = 1 ∧ 2 < SECP256K1_ORDER_N ∧
    secp256k1Curve.OnCurve secp256k1G ∧
    secp256k1Curve.smul 1 secp256k1G = secp256k1G := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, rfl, rfl, by decide +kernel, by decide +kernel, by decide +kernel, rfl⟩

/-- `PrimeOrderGroup` for the `secp256k1` generator. Its four group fields are unproved:
    every multiple of `G` on the curve, `[a + b]G = [a]G + [b]G`, `[n]G = O`, and
    `[k]G ≠ O` for `0 < k < n`. The other four fields are theorems: the parities are in
    `secp256k1_checked_parameters`, and `p`, `n` are prime by `secp256k1FieldPrime_isPrime`
    and `secp256k1OrderPrime_isPrime`. -/
abbrev Secp256k1GroupLaws : Prop :=
  secp256k1Curve.PrimeOrderGroup secp256k1G SECP256K1_ORDER_N

/-- `Secp256k1GroupLaws` from the four group facts alone; both primality fields and both
    parity fields are discharged here. -/
theorem secp256k1GroupLaws_of_group_facts
    (onCurve : ∀ k, secp256k1Curve.OnCurve (secp256k1Curve.smul k secp256k1G))
    (smul_add : ∀ a b, secp256k1Curve.smul (a + b) secp256k1G =
      secp256k1Curve.add (secp256k1Curve.smul a secp256k1G) (secp256k1Curve.smul b secp256k1G))
    (order : secp256k1Curve.smul SECP256K1_ORDER_N secp256k1G = none)
    (exact : ∀ k, 0 < k → k < SECP256K1_ORDER_N → secp256k1Curve.smul k secp256k1G ≠ none) :
    Secp256k1GroupLaws where
  p_prime := secp256k1FieldPrime_isPrime
  p_odd := secp256k1_checked_parameters.2.2.2.1
  n_prime := secp256k1OrderPrime_isPrime
  n_odd := secp256k1_checked_parameters.2.2.2.2.2.2.2.1
  onCurve := onCurve
  smul_add := smul_add
  order := order
  exact := exact

end Weierstrass

/-- The `secp256k1` projection: `xOf s` and `yParity s` are the affine `x`-coordinate
    and the parity of the affine `y`-coordinate of the curve point `[s]G`. It exists
    under `Weierstrass.Secp256k1GroupLaws`, which this file does not prove. -/
def secp256k1TaprootProjection (h : Weierstrass.Secp256k1GroupLaws) :
    TaprootCurveProjection SECP256K1_ORDER_N (Option Nat) :=
  h.projection

/-- The Taproot statement about `secp256k1` curve points, conditional on
    `Weierstrass.Secp256k1GroupLaws`: among canonical scalars, `[s₁]G` and `[s₂]G` have
    one affine `x`-coordinate exactly when `s₂ = s₁` or `s₂ = n - s₁`, negating the
    scalar flips the parity of the affine `y`-coordinate, and `x` together with that
    parity determines the scalar. -/
theorem secp256k1_xonly_parity_on_curve_points (h : Weierstrass.Secp256k1GroupLaws) :
    (∀ s1 s2 : BitVec 256,
      requireCanonicalScalar .Secp256k1 s1 = true →
      requireCanonicalScalar .Secp256k1 s2 = true →
      (Weierstrass.Point.x (Weierstrass.secp256k1Curve.smul s1.toNat Weierstrass.secp256k1G) =
        Weierstrass.Point.x (Weierstrass.secp256k1Curve.smul s2.toNat Weierstrass.secp256k1G) ↔
        taprootXOnlySameX s1 s2)) ∧
    (∀ s : BitVec 256,
      requireCanonicalScalar .Secp256k1 s = true →
      Weierstrass.Point.yOdd
          (Weierstrass.secp256k1Curve.smul (secpNegScalar s).toNat Weierstrass.secp256k1G) =
        !(Weierstrass.Point.yOdd
          (Weierstrass.secp256k1Curve.smul s.toNat Weierstrass.secp256k1G))) ∧
    (∀ s1 s2 : BitVec 256,
      requireCanonicalScalar .Secp256k1 s1 = true →
      requireCanonicalScalar .Secp256k1 s2 = true →
      Weierstrass.Point.x (Weierstrass.secp256k1Curve.smul s1.toNat Weierstrass.secp256k1G) =
        Weierstrass.Point.x (Weierstrass.secp256k1Curve.smul s2.toNat Weierstrass.secp256k1G) →
      Weierstrass.Point.yOdd (Weierstrass.secp256k1Curve.smul s1.toNat Weierstrass.secp256k1G) =
        Weierstrass.Point.yOdd (Weierstrass.secp256k1Curve.smul s2.toNat Weierstrass.secp256k1G) →
      s1 = s2) :=
  ⟨(secp256k1TaprootProjection h).sameX_iff_canonical,
    (secp256k1TaprootProjection h).yParity_neg_canonical,
    (taproot_even_y_parity_restores_canonical_injectivity (secp256k1TaprootProjection h)).2.1⟩

/-- RFC 8032 / SLIP-0010 Ed25519 scalar clamping on 32 little-endian digest bytes (`legacy.rs:260-262, 283-285`):
    clears low 3 bits (`h[0] &= 248`), clears bit 255 (`h[31] &= 127`), and sets bit 254 (`h[31] |= 64`). -/
def clampEd25519Nat (n : Nat) : Nat :=
  2 ^ 254 + ((n % (2 ^ 254)) / 8) * 8

theorem clampEd25519Nat_bounds (n : Nat) :
    2 ^ 254 ≤ clampEd25519Nat n ∧
    clampEd25519Nat n < 2 ^ 255 ∧
    clampEd25519Nat n % 8 = 0 ∧
    clampEd25519Nat n < 2 ^ 256 := by
  unfold clampEd25519Nat
  have hMod : n % (2 ^ 254) < 2 ^ 254 := Nat.mod_lt n (Nat.two_pow_pos 254)
  have h254Div8 : (2 : Nat) ^ 254 = 8 * (2 ^ 251) := by decide
  have h255 : (2 : Nat) ^ 255 = 2 ^ 254 + 2 ^ 254 := by decide
  have h256 : (2 : Nat) ^ 255 < 2 ^ 256 := by decide
  refine ⟨by omega, by omega, by omega, by omega⟩

/-- Clamped 256-bit Ed25519 scalar (`2^254 ≤ clamped < 2^255` and `clamped % 8 = 0`). -/
def clampEd25519Bytes32 (raw : BitVec 256) : BitVec 256 :=
  BitVec.ofNatLT (clampEd25519Nat raw.toNat) (clampEd25519Nat_bounds raw.toNat).2.2.2

/-- Modular reduction modulo `ED_ORDER` (`scalar.rs:150-159`, `legacy.rs:287`). -/
def reduceEd25519Order (x : BitVec 256) : BitVec 256 :=
  BitVec.ofNat 256 (x.toNat % ED25519_ORDER_L)

/-- Complete SLIP-0010 Ed25519 scalar normalization from the lower 32 bytes of `SHA-512(seed)` (`legacy.rs:281-289`). -/
def normalizeSlip0010Ed25519Scalar (sha512Lo32 : BitVec 256) : BitVec 256 :=
  reduceEd25519Order (clampEd25519Bytes32 sha512Lo32)

theorem clampEd25519Bytes32_bits_and_range (raw : BitVec 256) :
    2 ^ 254 ≤ (clampEd25519Bytes32 raw).toNat ∧
    (clampEd25519Bytes32 raw).toNat < 2 ^ 255 ∧
    (clampEd25519Bytes32 raw).toNat % 8 = 0 ∧
    (clampEd25519Bytes32 raw).getLsbD 0 = false ∧
    (clampEd25519Bytes32 raw).getLsbD 1 = false ∧
    (clampEd25519Bytes32 raw).getLsbD 2 = false ∧
    (clampEd25519Bytes32 raw).getLsbD 254 = true ∧
    (clampEd25519Bytes32 raw).getLsbD 255 = false := by
  have hb := clampEd25519Nat_bounds raw.toNat
  have hToNat : (clampEd25519Bytes32 raw).toNat = clampEd25519Nat raw.toNat := rfl
  refine ⟨by rw [hToNat]; exact hb.1,
          by rw [hToNat]; exact hb.2.1,
          by rw [hToNat]; exact hb.2.2.1, ?_, ?_, ?_, ?_, ?_⟩
  · change (clampEd25519Nat raw.toNat).testBit 0 = false
    rw [Nat.testBit_zero]
    have hMod8 := hb.2.2.1
    have : clampEd25519Nat raw.toNat % 2 = 0 := by omega
    rw [this]; decide
  · change (clampEd25519Nat raw.toNat).testBit 1 = false
    rw [Nat.testBit_succ, Nat.testBit_zero]
    have hMod8 := hb.2.2.1
    have : (clampEd25519Nat raw.toNat / 2) % 2 = 0 := by omega
    rw [this]; decide
  · change (clampEd25519Nat raw.toNat).testBit 2 = false
    rw [Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_zero]
    have hMod8 := hb.2.2.1
    have : ((clampEd25519Nat raw.toNat / 2) / 2) % 2 = 0 := by omega
    rw [this]; decide
  · change (clampEd25519Nat raw.toNat).testBit 254 = true
    rw [Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq]
    have hGe := hb.1
    have hLt := hb.2.1
    have h255 : (2 : Nat) ^ 255 = 2 * (2 ^ 254) := by decide
    have hDiv : clampEd25519Nat raw.toNat / (2 ^ 254) = 1 := by omega
    rw [hDiv]
  · change (clampEd25519Nat raw.toNat).testBit 255 = false
    rw [Nat.testBit_eq_decide_div_mod_eq, decide_eq_false_iff_not]
    have hLt := hb.2.1
    have hDiv : clampEd25519Nat raw.toNat / (2 ^ 255) = 0 := Nat.div_eq_of_lt hLt
    rw [hDiv]; omega

/-- **SLIP-0010 Ed25519 Normalization Totality (`slip0010_ed25519_clamped_canonical_nonzero`)**:
    For **every** 32-byte digest `raw : BitVec 256`, `normalizeSlip0010Ed25519Scalar raw` is
    strictly nonzero and `< ED25519_ORDER_L` (`requireCanonicalScalar .Ed25519 = true`), because
    `8 ∣ clamped`, `0 < clamped < 8 * ED25519_ORDER_L`, and `ED25519_ORDER_L % 8 = 5`. -/
theorem slip0010_ed25519_clamped_canonical_nonzero (raw : BitVec 256) :
    requireCanonicalScalar .Ed25519 (normalizeSlip0010Ed25519Scalar raw) = true := by
  have hOrd := curve_orders_match_le_limbs_and_bounds
  have hClamp := clampEd25519Nat_bounds raw.toNat
  let c := clampEd25519Nat raw.toNat
  have hcGe : 2 ^ 254 ≤ c := hClamp.1
  have hcLt : c < 2 ^ 255 := hClamp.2.1
  have hcMod8 : c % 8 = 0 := hClamp.2.2.1
  have hOrdGt : 2 ^ 252 < ED25519_ORDER_L := hOrd.2.2.2.2.2.1
  have hOrdLt256 : ED25519_ORDER_L < 2 ^ 256 :=
    Nat.lt_trans hOrd.2.2.2.2.2.2.1 (by decide : 2 ^ 253 < 2 ^ 256)
  have hOrdMod8 : ED25519_ORDER_L % 8 = 5 := hOrd.2.2.2.2.2.2.2.2
  have hOrdPos : 0 < ED25519_ORDER_L := Nat.lt_trans (Nat.two_pow_pos 252) hOrdGt
  have hRemLtOrd : c % ED25519_ORDER_L < ED25519_ORDER_L :=
    Nat.mod_lt c hOrdPos
  have hRemNeZero : c % ED25519_ORDER_L ≠ 0 := by
    intro hZero
    have hDivEq : ED25519_ORDER_L * (c / ED25519_ORDER_L) + c % ED25519_ORDER_L = c :=
      Nat.div_add_mod c ED25519_ORDER_L
    rw [hZero, Nat.add_zero] at hDivEq
    let q := c / ED25519_ORDER_L
    have hEqC : ED25519_ORDER_L * q = c := hDivEq
    have h8L : 2 ^ 255 < ED25519_ORDER_L * 8 := by unfold ED25519_ORDER_L; decide
    have hPos254 : 0 < 2 ^ 254 := Nat.two_pow_pos 254
    have hqNot0 : q ≠ 0 := by
      intro hq0
      rw [hq0, Nat.mul_zero] at hEqC
      omega
    have hqLt8 : q < 8 := by
      cases (inferInstance : Decidable (q < 8)) with
      | isTrue h => exact h
      | isFalse hGe =>
        have hLe : ED25519_ORDER_L * 8 ≤ ED25519_ORDER_L * q :=
          Nat.mul_le_mul_left ED25519_ORDER_L (by omega)
        rw [hEqC] at hLe
        have hContr : 2 ^ 255 < c := Nat.lt_of_lt_of_le h8L hLe
        omega
    have hMulMod : (ED25519_ORDER_L * q) % 8 = ((ED25519_ORDER_L % 8) * (q % 8)) % 8 :=
      Nat.mul_mod ED25519_ORDER_L q 8
    rw [hEqC, hcMod8, hOrdMod8] at hMulMod
    match q with
    | 0 => exact hqNot0 rfl
    | 1 | 2 | 3 | 4 | 5 | 6 | 7 => simp at hMulMod
    | _ + 8 => omega
  rw [requireCanonicalScalar_iff]
  unfold normalizeSlip0010Ed25519Scalar reduceEd25519Order clampEd25519Bytes32
  have hToNat : (BitVec.ofNatLT c hClamp.2.2.2).toNat = c := rfl
  rw [hToNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans hRemLtOrd hOrdLt256)]
  exact ⟨Nat.pos_of_ne_zero hRemNeZero, hRemLtOrd⟩

/-! ## 1. Exact `Pallas` (`Orchard`) & `BLS12-381` (`Beacon`) Parameters and Limb Equivalence -/

@[expose] def p_pallas : Nat := 0x40000000000000000000000000000000224698fc094cf91b992d30ed00000001
@[expose] def q_pallas : Nat := 0x40000000000000000000000000000000224698fc0994a8dd8c46eb2100000001
@[expose] def p_bls381 : Nat :=
  0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab
@[expose] def r_bls381 : Nat := 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001

def limbs4LeNat (limbs : Fin 4 → UInt64) : Nat :=
  (limbs ⟨0, by decide⟩).toNat + (limbs ⟨1, by decide⟩).toNat * (2 ^ 64) +
  (limbs ⟨2, by decide⟩).toNat * (2 ^ 128) + (limbs ⟨3, by decide⟩).toNat * (2 ^ 192)

def limbs6LeToNat (limbs : Fin 6 → UInt64) : Nat :=
  (limbs ⟨0, by decide⟩).toNat + (limbs ⟨1, by decide⟩).toNat * (2 ^ 64) +
  (limbs ⟨2, by decide⟩).toNat * (2 ^ 128) + (limbs ⟨3, by decide⟩).toNat * (2 ^ 192) +
  (limbs ⟨4, by decide⟩).toNat * (2 ^ 256) + (limbs ⟨5, by decide⟩).toNat * (2 ^ 320)

def pallasPLimbsLe : Fin 4 → UInt64
  | ⟨0, _⟩ => 0x992d30ed00000001 | ⟨1, _⟩ => 0x224698fc094cf91b | ⟨2, _⟩ => 0 | ⟨3, _⟩ => 0x4000000000000000
def pallasQLimbsLe : Fin 4 → UInt64
  | ⟨0, _⟩ => 0x8c46eb2100000001 | ⟨1, _⟩ => 0x224698fc0994a8dd | ⟨2, _⟩ => 0 | ⟨3, _⟩ => 0x4000000000000000
def bls381PLimbsLe : Fin 6 → UInt64
  | ⟨0, _⟩ => 0xb9feffffffffaaab | ⟨1, _⟩ => 0x1eabfffeb153ffff | ⟨2, _⟩ => 0x6730d2a0f6b0f624
  | ⟨3, _⟩ => 0x64774b84f38512bf | ⟨4, _⟩ => 0x4b1ba7b6434bacd7 | ⟨5, _⟩ => 0x1a0111ea397fe69a
def bls381RLimbsLe : Fin 4 → UInt64
  | ⟨0, _⟩ => 0xffffffff00000001 | ⟨1, _⟩ => 0x53bda402fffe5bfe
  | ⟨2, _⟩ => 0x3339d80809a1d805 | ⟨3, _⟩ => 0x73eda753299d7d48

/-- The RCB and affine APIs share one short-Weierstrass parameter carrier. -/
abbrev SwCurve := Weierstrass.Curve

abbrev SwPoint := Option (Nat × Nat)

@[expose] def SwCurve.onCurve (C : SwCurve) : SwPoint → Bool
  | none => true
  | some (x, y) => decide (x < C.p) && decide (y < C.p) && (((y * y) % C.p) == ((x * x * x + C.a * x + C.b) % C.p))

@[expose] def SwCurve.neg (C : SwCurve) : SwPoint → SwPoint
  | none => none | some (x, y) => some (x, (C.p - y) % C.p)

def pallasCurve : SwCurve := { p := p_pallas, a := 0, b := 5 }
def orchardSpendAuthG : SwPoint :=
  some (0x375523b328f1d6063b8d187c3e5f445f0c7f0ce37b70a10c8d1a7284b875c963,
        0x1ad0357fdf1a66db7b10bcfcfed624fbdfc914fec005bdd84ce33e817b0c3bc9)
def pastaPallasG : SwPoint := some (p_pallas - 1, 2)
def bls381Curve : SwCurve := { p := p_bls381, a := 0, b := 4 }
def bls381G1 : SwPoint :=
  some (0x17f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb,
        0x08b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1)

private def pow2_384 : Nat := (2 ^ 192) * (2 ^ 192)
private theorem pow2_384_eq : pow2_384 = 2 ^ 384 := by rw [pow2_384, ← Nat.pow_add]

theorem pallas_and_bls381_limbs_and_bit_bounds :
    limbs4LeNat pallasPLimbsLe = p_pallas ∧ limbs4LeNat pallasQLimbsLe = q_pallas ∧
    limbs6LeToNat bls381PLimbsLe = p_bls381 ∧ limbs4LeNat bls381RLimbsLe = r_bls381 ∧
    2 ^ 254 < p_pallas ∧ p_pallas < 2 ^ 255 ∧ p_pallas % 2 = 1 ∧
    2 ^ 254 < q_pallas ∧ q_pallas < 2 ^ 255 ∧ q_pallas % 2 = 1 ∧
    2 ^ 380 < p_bls381 ∧ p_bls381 < 2 ^ 381 ∧ p_bls381 % 4 = 3 ∧
    2 ^ 254 < r_bls381 ∧ r_bls381 < 2 ^ 255 ∧ r_bls381 % 2 = 1 := by
  unfold limbs4LeNat limbs6LeToNat pallasPLimbsLe pallasQLimbsLe bls381PLimbsLe bls381RLimbsLe
    p_pallas q_pallas p_bls381 r_bls381
  decide +kernel

/-! ## 2. Constructive Lucas–Pratt Primality Certificates (`0 native_decide`, `0 Classical.choice`) -/

@[expose] def IsPrimeMod (p : Nat) : Prop := 2 ≤ p ∧ ∀ d : Nat, d ∣ p → d = 1 ∨ d = p

theorem IsPrimeMod.dvd_mul {p a b : Nat} (hp : IsPrimeMod p) (h : p ∣ a * b) (hna : ¬ (p ∣ a)) : p ∣ b := by
  rcases hp.2 (Nat.gcd p a) (Nat.gcd_dvd_left p a) with h1 | hpg
  · exact Nat.Coprime.dvd_of_dvd_mul_left h1 h
  · exact False.elim (hna (hpg ▸ Nat.gcd_dvd_right p a))

private def strictNat (n : Nat) (k : Nat → Nat) : Nat := match n with | 0 => k 0 | m + 1 => k (m + 1)
private theorem strictNat_eq (n : Nat) (k : Nat → Nat) : strictNat n k = k n := by cases n <;> rfl

/-- Eager binary modular exponentiation `base ^ exp % m` in `fuel` squaring steps. -/
def lucasPowMod : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, m => 1 % m
  | fuel + 1, base, exp, m =>
    if exp = 0 then 1 % m
    else strictNat (lucasPowMod fuel base (exp / 2) m) fun half =>
      strictNat ((half * half) % m) fun sq => if exp % 2 = 1 then (sq * (base % m)) % m else sq

private theorem pow_two_mul_local (b k : Nat) : b ^ (2 * k) = (b ^ k) * (b ^ k) := by
  rw [Nat.mul_comm 2 k, Nat.pow_mul, Nat.pow_succ, Nat.pow_one]

theorem lucasPowMod_eq_pow_mod :
    ∀ (fuel base exp m : Nat), exp < 2 ^ fuel → lucasPowMod fuel base exp m = (base ^ exp) % m
  | 0, _, exp, m, hlt => by have he0 : exp = 0 := by simp at hlt; omega
                            subst he0; simp [lucasPowMod]
  | fuel + 1, base, exp, m, hlt => by
    simp only [lucasPowMod]
    if h0 : exp = 0 then subst h0; simp
    else
      simp only [h0, ↓reduceIte, strictNat_eq]
      have hexpHalf : exp / 2 < 2 ^ fuel := by rw [Nat.pow_succ] at hlt; omega
      have ih := lucasPowMod_eq_pow_mod fuel base (exp / 2) m hexpHalf
      have hsq : ((lucasPowMod fuel base (exp / 2) m) * (lucasPowMod fuel base (exp / 2) m)) % m =
          (base ^ (2 * (exp / 2))) % m := by rw [ih, ← Nat.mul_mod, ← pow_two_mul_local]
      rcases (by omega : exp % 2 = 0 ∨ exp % 2 = 1) with hr0 | hr1
      · simp only [hr0, show ¬ (0 = 1) by decide, ↓reduceIte]; rw [hsq, show 2 * (exp / 2) = exp by omega]
      · simp only [hr1, ↓reduceIte]
        conv => rhs; rw [show exp = 2 * (exp / 2) + 1 by omega, Nat.pow_add, Nat.pow_one, Nat.mul_mod]
        rw [hsq]

private def powNatStrict (b : Nat) : Nat → Nat
  | 0 => 1 | e + 1 => strictNat (powNatStrict b e) fun p => b * p
private theorem powNatStrict_eq (b : Nat) : ∀ e : Nat, powNatStrict b e = b ^ e
  | 0 => rfl | e + 1 => by simp only [powNatStrict, strictNat_eq, powNatStrict_eq b e, Nat.pow_succ, Nat.mul_comm]

def lucasFacProd : List (Nat × Nat) → Nat
  | [] => 1
  | (q, e) :: rest => strictNat (powNatStrict q e) fun qe => strictNat (lucasFacProd rest) fun tail => qe * tail

structure PrattCert where
  n : Nat
  g : Nat
  facs : List (Nat × Nat)

def checkPrattStep (knownPrimes : List Nat) (c : PrattCert) : Bool :=
  decide (3 ≤ c.n) && decide (c.n < pow2_384) && (lucasFacProd c.facs == c.n - 1) &&
  c.facs.all (fun qe => decide (1 ≤ qe.2) && knownPrimes.any (fun p => p == qe.1)) &&
  (lucasPowMod 384 c.g (c.n - 1) c.n == 1) &&
  c.facs.all (fun qe => lucasPowMod 384 c.g ((c.n - 1) / qe.1) c.n != 1)

def checkPrattDAG : List Nat → List PrattCert → Bool
  | _, [] => true | known, c :: rest => checkPrattStep known c && checkPrattDAG (c.n :: known) rest

private def minPrimeDivAux (n d : Nat) : Nat → Nat
  | 0 => n | fuel + 1 => if n % d = 0 then d else minPrimeDivAux n (d + 1) fuel
private def minPrimeDiv (n : Nat) : Nat := if n < 2 then n else minPrimeDivAux n 2 n

private theorem minPrimeDivAux_spec :
    ∀ (fuel n d : Nat), 2 ≤ n → 2 ≤ d → n ≤ d + fuel → (∀ k : Nat, 2 ≤ k → k < d → ¬ (k ∣ n)) →
      let q := minPrimeDivAux n d fuel
      2 ≤ q ∧ q ∣ n ∧ (∀ k : Nat, 2 ≤ k → k < q → ¬ (k ∣ n))
  | 0, n, d, hn2, _, hle, hno => by
    dsimp only [minPrimeDivAux]; exact ⟨hn2, Nat.dvd_refl n, fun k hk2 hklt => hno k hk2 (by omega)⟩
  | fuel + 1, n, d, hn2, hd, hle, hno => by
    dsimp only [minPrimeDivAux]; split
    · next hmod => exact ⟨hd, Nat.dvd_of_mod_eq_zero hmod, hno⟩
    · next hmod =>
      refine minPrimeDivAux_spec fuel n (d + 1) hn2 (by omega) (by omega) (fun k hk2 hklt => ?_)
      exact if hkd : k = d then fun hdvd => hmod (Nat.mod_eq_zero_of_dvd (hkd ▸ hdvd)) else hno k hk2 (by omega)

private theorem minPrimeDiv_isPrime {n : Nat} (hn : 2 ≤ n) : IsPrimeMod (minPrimeDiv n) ∧ minPrimeDiv n ∣ n := by
  have hge : ¬ n < 2 := by omega
  unfold minPrimeDiv; simp only [hge, ↓reduceIte]
  obtain ⟨hq2, hqdvd, hqmin⟩ := minPrimeDivAux_spec n n 2 hn (by decide) (by omega) (by intros; omega)
  refine ⟨⟨hq2, fun d hd => ?_⟩, hqdvd⟩
  if hd1 : d = 1 then exact .inl hd1
  else if hdq : d = minPrimeDivAux n 2 n then exact .inr hdq
  else
    have := Nat.pos_of_dvd_of_pos hd (by omega); have := Nat.le_of_dvd (by omega) hd
    exact False.elim (hqmin d (by omega) (by omega) (Nat.dvd_trans hd hqdvd))

private theorem prime_dvd_pow {p q : Nat} (hp : IsPrimeMod p) : ∀ e : Nat, p ∣ q ^ e → p ∣ q
  | 0, hd => by rw [Nat.pow_zero] at hd; have := Nat.le_of_dvd (by decide) hd; have := hp.1; omega
  | e + 1, hd => by
    rw [Nat.pow_succ] at hd
    exact if hpq : p ∣ q then hpq else prime_dvd_pow hp e (hp.dvd_mul (Nat.mul_comm _ _ ▸ hd) hpq)

private theorem prime_mem_of_dvd_facProd {p : Nat} (hp : IsPrimeMod p) :
    ∀ {facs : List (Nat × Nat)}, (∀ qe ∈ facs, IsPrimeMod qe.1) → p ∣ lucasFacProd facs → ∃ qe ∈ facs, qe.1 = p
  | [], _, hd => by dsimp only [lucasFacProd] at hd; have := Nat.le_of_dvd (by decide) hd; have := hp.1; omega
  | (q, e) :: rest, hPrimes, hd => by
    simp only [lucasFacProd, strictNat_eq, powNatStrict_eq] at hd
    if hdq : p ∣ q ^ e then
      rcases (hPrimes (q, e) (.head _)).2 p (prime_dvd_pow hp e hdq) with hp1 | hpEq
      · have := hp.1; omega
      · exact ⟨(q, e), .head _, hpEq.symm⟩
    else
      obtain ⟨qe, hMem, hEq⟩ := prime_mem_of_dvd_facProd hp (fun x hx => hPrimes x (.tail _ hx)) (hp.dvd_mul hd hdq)
      exact ⟨qe, .tail _ hMem, hEq⟩

private def minOrderAux (g N cur : Nat) : Nat → Nat
  | 0 => cur | fuel + 1 => if (g ^ cur) % N = 1 then cur else minOrderAux g N (cur + 1) fuel

private theorem minOrderAux_spec (g N : Nat) :
    ∀ (fuel cur : Nat), 1 ≤ cur → (g ^ (cur + fuel)) % N = 1 → (∀ k : Nat, 1 ≤ k → k < cur → (g ^ k) % N ≠ 1) →
      let d := minOrderAux g N cur fuel
      1 ≤ d ∧ d ≤ cur + fuel ∧ (g ^ d) % N = 1 ∧ (∀ k : Nat, 1 ≤ k → k < d → (g ^ k) % N ≠ 1)
  | 0, cur, hcur, hEnd, hMin => by dsimp only [minOrderAux]; exact ⟨hcur, Nat.le_refl cur, Nat.add_zero cur ▸ hEnd, hMin⟩
  | fuel + 1, cur, hcur, hEnd, hMin => by
    dsimp only [minOrderAux]; split
    · next h1 => exact ⟨hcur, by omega, h1, hMin⟩
    · next h1 =>
      have res := minOrderAux_spec g N fuel (cur + 1) (by omega)
        (by rwa [show (cur + 1) + fuel = cur + (fuel + 1) by omega])
        (fun k hk1 hklt => if hkc : k = cur then hkc ▸ h1 else hMin k hk1 (by omega))
      exact ⟨res.1, by omega, res.2.2.1, res.2.2.2⟩

private theorem pow_mod_eq_one_rep {a N : Nat} (hN : 2 ≤ N) (ha : a % N = 1) : ∀ q : Nat, (a ^ q) % N = 1
  | 0 => Nat.mod_eq_of_lt hN
  | q + 1 => by rw [Nat.pow_succ, Nat.mul_mod, pow_mod_eq_one_rep hN ha q, ha]; exact Nat.mod_eq_of_lt hN

private theorem order_dvd_of_pow_eq_one {g N d0 m : Nat} (hN : 2 ≤ N) (hd0 : 1 ≤ d0) (hPow0 : (g ^ d0) % N = 1)
    (hMin : ∀ k : Nat, 1 ≤ k → k < d0 → (g ^ k) % N ≠ 1) (hPowM : (g ^ m) % N = 1) : d0 ∣ m := by
  have hm' : (g ^ (d0 * (m / d0) + m % d0)) % N = 1 := (Nat.div_add_mod m d0).symm ▸ hPowM
  rw [Nat.pow_add, Nat.pow_mul, Nat.mul_mod, pow_mod_eq_one_rep hN hPow0 (m / d0), Nat.one_mul, Nat.mod_mod] at hm'
  exact if hRem0 : m % d0 = 0 then Nat.dvd_of_mod_eq_zero hRem0
        else False.elim (hMin (m % d0) (by omega) (Nat.mod_lt m (by omega)) hm')

private def eraseOne (v : Nat) : List Nat → List Nat
  | [] => [] | y :: ys => if y = v then ys else y :: eraseOne v ys

private theorem mem_of_mem_eraseOne {v z : Nat} : ∀ {ys : List Nat}, z ∈ eraseOne v ys → z ∈ ys
  | [], h => nomatch h
  | y :: ys, h => by
    dsimp only [eraseOne] at h; split at h
    · exact .tail _ h
    · cases h with | head => exact .head _ | tail _ ht => exact .tail _ (mem_of_mem_eraseOne ht)

private theorem eraseOne_spec {v : Nat} : ∀ {ys : List Nat}, ys.Nodup → v ∈ ys →
    (eraseOne v ys).length + 1 = ys.length ∧ (eraseOne v ys).Nodup ∧ (∀ z : Nat, z ≠ v → z ∈ ys → z ∈ eraseOne v ys)
  | [], _, hmem => nomatch hmem
  | y :: ys, .cons hrel hnd, hmem => by
    dsimp only [eraseOne]; split
    · next hy =>
      subst hy; refine ⟨rfl, hnd, fun z hzne hz => ?_⟩
      cases hz with | head => exact False.elim (hzne rfl) | tail _ ht => exact ht
    · next hy =>
      have hvTail : v ∈ ys := by cases hmem with | head => exact False.elim (hy rfl) | tail _ ht => exact ht
      obtain ⟨hlen, hnd', hsub⟩ := eraseOne_spec hnd hvTail
      refine ⟨by simp only [List.length_cons]; omega,
        .cons (fun b hb heq => hrel b (mem_of_mem_eraseOne hb) heq) hnd', fun z hzne hz => ?_⟩
      cases hz with | head => exact .head _ | tail _ ht => exact .tail _ (hsub z hzne ht)

private theorem mem_of_nodup_subset_eq_length : ∀ {xs ys : List Nat}, xs.Nodup → ys.Nodup →
    xs.length = ys.length → (∀ x ∈ xs, x ∈ ys) → ∀ y ∈ ys, y ∈ xs
  | [], [], _, _, _, _, _, hy => nomatch hy
  | [], _ :: _, _, _, hlen, _, _, _ => nomatch hlen
  | x :: xs, ys, .cons hrel hndX, hndY, hlen, hsub, y, hy => by
    if hyx : y = x then subst hyx; exact .head _
    else
      obtain ⟨hlenE, hndE, hmemE⟩ := eraseOne_spec hndY (hsub x (.head _))
      simp only [List.length_cons] at hlen
      exact .tail _ (mem_of_nodup_subset_eq_length hndX hndE (by omega)
        (fun z hz => hmemE z (fun heq => hrel z hz heq.symm) (hsub z (.tail _ hz))) y (hmemE y hyx hy))

/-- **Lucas–Pratt Theorem (`isPrime_of_lucas_pratt`)**: exact prime-factor order witnesses imply `IsPrimeMod N`. -/
theorem isPrime_of_lucas_pratt {N g : Nat} {facs : List (Nat × Nat)}
    (hN3 : 3 ≤ N) (hProd : lucasFacProd facs = N - 1) (hPrimes : ∀ qe ∈ facs, IsPrimeMod qe.1)
    (hFermat : (g ^ (N - 1)) % N = 1) (hOrder : ∀ qe ∈ facs, (g ^ ((N - 1) / qe.1)) % N ≠ 1) : IsPrimeMod N := by
  have hN2 : 2 ≤ N := by omega
  obtain ⟨hd1, hdLe, hdPow, hdMin⟩ := minOrderAux_spec g N (N - 2) 1 (by decide)
    (by rwa [show 1 + (N - 2) = N - 1 by omega]) (by intros; omega)
  let d0 := minOrderAux g N 1 (N - 2)
  have hdDvdNm1 : d0 ∣ (N - 1) := order_dvd_of_pow_eq_one hN2 hd1 hdPow hdMin hFermat
  have hdEqNm1 : d0 = N - 1 := by
    if hEq : d0 = N - 1 then exact hEq
    else
      exfalso; obtain ⟨c, hc⟩ := hdDvdNm1
      have hc2 : 2 ≤ c := by
        if hc0 : c = 0 then rw [hc0, Nat.mul_zero] at hc; omega
        else if hc1 : c = 1 then rw [hc1, Nat.mul_one] at hc; exact False.elim (hEq hc.symm)
        else omega
      obtain ⟨hpPrime, c', hc'⟩ := minPrimeDiv_isPrime hc2
      let p := minPrimeDiv c
      have hNm1Eq : N - 1 = p * (d0 * c') := by rw [hc, hc', ← Nat.mul_assoc d0 p c', Nat.mul_comm d0 p, Nat.mul_assoc]
      obtain ⟨qe, hqeMem, hqeEq⟩ := prime_mem_of_dvd_facProd hpPrime hPrimes (by rw [hProd, hNm1Eq]; exact Nat.dvd_mul_right p _)
      refine hOrder qe hqeMem ?_
      rw [hqeEq, hNm1Eq, Nat.mul_comm p (d0 * c'), Nat.mul_div_left (d0 * c') (by have := hpPrime.1; omega), Nat.pow_mul]
      exact pow_mod_eq_one_rep hN2 hdPow c'
  have hdMinNm1 : ∀ k : Nat, 1 ≤ k → k < N - 1 → (g ^ k) % N ≠ 1 := hdEqNm1 ▸ hdMin
  let L := posRange (N - 1); let f := fun k : Nat => (g ^ k) % N
  have hMapMem : ∀ x ∈ L.map f, x ∈ L := by
    intro x hx; obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx; obtain ⟨hk1, hkHi⟩ := (mem_posRange_iff (n := N - 1)).1 hk
    have hfkLt : (g ^ k) % N < N := Nat.mod_lt _ (by omega)
    have hfkPos : 1 ≤ (g ^ k) % N := by
      if hz : (g ^ k) % N = 0 then
        have hdvdNm1 : N ∣ g ^ (N - 1) := by
          rw [show N - 1 = k + (N - 1 - k) by omega, Nat.pow_add]
          exact Nat.dvd_mul_right_of_dvd (Nat.dvd_of_mod_eq_zero hz) _
        have := Nat.mod_eq_zero_of_dvd hdvdNm1; omega
      else omega
    exact (mem_posRange_iff (n := N - 1)).2 ⟨hfkPos, by dsimp only [f]; omega⟩
  have hInjStep : ∀ i j : Nat, 1 ≤ i → i < j → j ≤ N - 1 → f i = f j → False := by
    intro i j hi1 hij hjHi hEqF
    have hMulEq : ((g ^ j % N) * (g ^ (N - 1 - i) % N)) % N = ((g ^ i % N) * (g ^ (N - 1 - i) % N)) % N := by
      dsimp only [f] at hEqF; rw [hEqF]
    rw [← Nat.mul_mod, ← Nat.mul_mod, ← Nat.pow_add, ← Nat.pow_add,
        show i + (N - 1 - i) = N - 1 by omega, show j + (N - 1 - i) = (N - 1) + (j - i) by omega,
        Nat.pow_add, Nat.mul_mod, hFermat, Nat.one_mul, Nat.mod_mod] at hMulEq
    exact hdMinNm1 (j - i) (by omega) (by omega) hMulEq
  have hMapNodup : (L.map f).Nodup := by
    have aux : ∀ {xs : List Nat}, xs.Nodup → (∀ z ∈ xs, z ∈ L) → (xs.map f).Nodup := by
      intro xs hnd hxs; induction hnd with
      | nil => exact .nil
      | @cons a rest hrel _ ih =>
        refine .cons (fun b hb heq => ?_) (ih (fun z hz => hxs z (.tail _ hz)))
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hb
        obtain ⟨ha1, haHi⟩ := (mem_posRange_iff (n := N - 1)).1 (hxs a (.head _))
        obtain ⟨hy1, hyHi⟩ := (mem_posRange_iff (n := N - 1)).1 (hxs y (.tail _ hy))
        rcases Nat.lt_trichotomy a y with hlt | hEq | hgt
        · exact hInjStep a y ha1 hlt hyHi heq
        · exact hrel y hy hEq
        · exact hInjStep y a hy1 hgt haHi heq.symm
    exact aux (posRange_nodup (N - 1)) (fun z hz => hz)
  have hSurj := mem_of_nodup_subset_eq_length hMapNodup (posRange_nodup (N - 1)) (List.length_map f) hMapMem
  refine ⟨hN2, fun d hd => ?_⟩
  if hd1' : d = 1 then exact .inl hd1'
  else if hdN : d = N then exact .inr hdN
  else
    exfalso
    have hdPos := Nat.pos_of_dvd_of_pos hd (by omega); have hdLeN := Nat.le_of_dvd (by omega) hd
    obtain ⟨k, hkMem, hfkEq⟩ := List.mem_map.1 (hSurj d ((mem_posRange_iff (n := N - 1)).2 ⟨by omega, by omega⟩))
    obtain ⟨hk1, hkHi⟩ := (mem_posRange_iff (n := N - 1)).1 hkMem; dsimp only [f] at hfkEq
    have hDivK := Nat.div_add_mod (g ^ k) N; rw [hfkEq] at hDivK
    have hdGk : d ∣ g ^ k := by rw [← hDivK]; exact Nat.dvd_add (Nat.dvd_trans hd (Nat.dvd_mul_right N _)) (Nat.dvd_refl d)
    have hdGNm1 : d ∣ g ^ (N - 1) := by
      rw [show N - 1 = k + (N - 1 - k) by omega, Nat.pow_add]; exact Nat.dvd_mul_right_of_dvd hdGk _
    have hDivNm1 := Nat.div_add_mod (g ^ (N - 1)) N; rw [hFermat] at hDivNm1
    obtain ⟨u, hu⟩ := hd; obtain ⟨v, hv⟩ := hdGNm1
    have hd1Dvd : d ∣ 1 := ⟨v - u * (g ^ (N - 1) / N), by rw [Nat.mul_sub, ← hv, ← Nat.mul_assoc d u _, ← hu]; omega⟩
    have := Nat.le_of_dvd (by decide) hd1Dvd; omega

theorem checkPrattStep_sound {known : List Nat} {c : PrattCert}
    (hKnown : ∀ p ∈ known, IsPrimeMod p) (hCheck : checkPrattStep known c = true) : IsPrimeMod c.n := by
  unfold checkPrattStep at hCheck
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, bne_iff_ne, List.all_eq_true, List.any_eq_true] at hCheck
  rcases hCheck with ⟨⟨⟨⟨⟨h3, hLt⟩, hProd⟩, hFacs⟩, hFerm⟩, hOrd⟩
  rw [pow2_384_eq] at hLt; have hExpNm1 : c.n - 1 < 2 ^ 384 := by omega
  rw [lucasPowMod_eq_pow_mod 384 c.g (c.n - 1) c.n hExpNm1] at hFerm
  refine isPrime_of_lucas_pratt h3 hProd (fun qe hMem => ?_) hFerm (fun qe hMem => ?_)
  · obtain ⟨_, p, hpMem, hpEq⟩ := hFacs qe hMem; exact hpEq ▸ hKnown p hpMem
  · have hDivLt : (c.n - 1) / qe.1 < 2 ^ 384 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hExpNm1
    have hNe := hOrd qe hMem; rwa [lucasPowMod_eq_pow_mod 384 c.g ((c.n - 1) / qe.1) c.n hDivLt] at hNe

theorem checkPrattDAG_sound : ∀ (certs : List PrattCert) (known : List Nat),
    (∀ p ∈ known, IsPrimeMod p) → checkPrattDAG known certs = true → ∀ c ∈ certs, IsPrimeMod c.n
  | [], _, _, _, _, hc => nomatch hc
  | c :: rest, known, hKnown, hOk, target, hMem => by
    unfold checkPrattDAG at hOk; rw [Bool.and_eq_true] at hOk
    have hcPrime : IsPrimeMod c.n := checkPrattStep_sound hKnown hOk.1
    cases hMem with
    | head => exact hcPrime
    | tail _ hTail =>
      refine checkPrattDAG_sound rest (c.n :: known) (fun p hp => ?_) hOk.2 target hTail
      cases hp with | head => exact hcPrime | tail _ hIn => exact hKnown p hIn

/-- Complete 139-node Lucas–Pratt certificate DAG covering `p_pallas`, `q_pallas`, `r_bls381`, and `p_bls381`. -/
def prattCerts : List PrattCert :=
  [ ⟨19, 2, [(2, 1), (3, 2)]⟩, ⟨7, 3, [(2, 1), (3, 1)]⟩, ⟨13, 2, [(2, 2), (3, 1)]⟩, ⟨5, 2, [(2, 2)]⟩, ⟨53, 2, [(2, 2), (13, 1)]⟩,
    ⟨79, 3, [(2, 1), (3, 1), (13, 1)]⟩, ⟨43, 3, [(2, 1), (3, 1), (7, 1)]⟩, ⟨19267, 3, [(2, 1), (3, 1), (13, 2), (19, 1)]⟩, ⟨17, 3, [(2, 4)]⟩,
    ⟨71, 7, [(2, 1), (5, 1), (7, 1)]⟩, ⟨173, 2, [(2, 2), (43, 1)]⟩, ⟨2557, 2, [(2, 2), (3, 2), (71, 1)]⟩, ⟨757, 2, [(2, 2), (3, 3), (7, 1)]⟩,
    ⟨73, 5, [(2, 3), (3, 2)]⟩, ⟨29, 2, [(2, 2), (7, 1)]⟩, ⟨97, 5, [(2, 5), (3, 1)]⟩, ⟨449, 3, [(2, 6), (7, 1)]⟩, ⟨31, 3, [(2, 1), (3, 1), (5, 1)]⟩,
    ⟨127, 3, [(2, 1), (3, 2), (7, 1)]⟩, ⟨41, 6, [(2, 3), (5, 1)]⟩, ⟨68477, 2, [(2, 2), (17, 1), (19, 1), (53, 1)]⟩,
    ⟨6091, 7, [(2, 1), (3, 1), (5, 1), (7, 1), (29, 1)]⟩, ⟨191, 19, [(2, 1), (5, 1), (19, 1)]⟩, ⟨233, 3, [(2, 3), (29, 1)]⟩,
    ⟨281, 3, [(2, 3), (5, 1), (7, 1)]⟩, ⟨113, 3, [(2, 4), (7, 1)]⟩, ⟨137, 3, [(2, 3), (17, 1)]⟩, ⟨409, 21, [(2, 3), (3, 1), (17, 1)]⟩,
    ⟨151, 6, [(2, 1), (3, 1), (5, 2)]⟩, ⟨8101, 6, [(2, 2), (3, 4), (5, 2)]⟩, ⟨6229, 2, [(2, 2), (3, 2), (173, 1)]⟩,
    ⟨1327, 3, [(2, 1), (3, 1), (13, 1), (17, 1)]⟩, ⟨241, 7, [(2, 4), (3, 1), (5, 1)]⟩, ⟨181, 2, [(2, 2), (3, 2), (5, 1)]⟩, ⟨11, 2, [(2, 1), (5, 1)]⟩,
    ⟨10177, 7, [(2, 6), (3, 1), (53, 1)]⟩, ⟨2508409, 11, [(2, 3), (3, 4), (7, 2), (79, 1)]⟩, ⟨23, 5, [(2, 1), (11, 1)]⟩, ⟨47, 5, [(2, 1), (23, 1)]⟩,
    ⟨89, 3, [(2, 3), (11, 1)]⟩, ⟨2531, 2, [(2, 1), (5, 1), (11, 1), (23, 1)]⟩, ⟨115603, 2, [(2, 1), (3, 1), (19267, 1)]⟩,
    ⟨61, 2, [(2, 2), (3, 1), (5, 1)]⟩, ⟨1381, 2, [(2, 2), (3, 1), (5, 1), (23, 1)]⟩, ⟨294793, 10, [(2, 3), (3, 1), (71, 1), (173, 1)]⟩,
    ⟨47737, 5, [(2, 3), (3, 3), (13, 1), (17, 1)]⟩, ⟨1607, 5, [(2, 1), (11, 1), (73, 1)]⟩, ⟨18329, 3, [(2, 3), (29, 1), (79, 1)]⟩,
    ⟨609743, 5, [(2, 1), (7, 1), (97, 1), (449, 1)]⟩, ⟨829, 2, [(2, 2), (3, 2), (23, 1)]⟩, ⟨59, 2, [(2, 1), (29, 1)]⟩,
    ⟨1973, 2, [(2, 2), (17, 1), (29, 1)]⟩, ⟨509, 2, [(2, 2), (127, 1)]⟩, ⟨413527, 3, [(2, 1), (3, 1), (41, 3)]⟩,
    ⟨958679, 7, [(2, 1), (7, 1), (68477, 1)]⟩, ⟨827, 2, [(2, 1), (7, 1), (59, 1)]⟩, ⟨5701177, 7, [(2, 3), (3, 2), (13, 1), (6091, 1)]⟩,
    ⟨31649, 3, [(2, 5), (23, 1), (43, 1)]⟩, ⟨523, 2, [(2, 1), (3, 2), (29, 1)]⟩, ⟨941, 2, [(2, 2), (5, 1), (47, 1)]⟩,
    ⟨1686913, 10, [(2, 7), (3, 1), (23, 1), (191, 1)]⟩, ⟨467, 2, [(2, 1), (233, 1)]⟩, ⟨3373, 5, [(2, 2), (3, 1), (281, 1)]⟩,
    ⟨25741, 6, [(2, 2), (3, 2), (5, 1), (11, 1), (13, 1)]⟩, ⟨179, 2, [(2, 1), (89, 1)]⟩, ⟨3037, 2, [(2, 2), (3, 1), (11, 1), (23, 1)]⟩,
    ⟨2741, 2, [(2, 2), (5, 1), (137, 1)]⟩, ⟨51376543, 3, [(2, 1), (3, 1), (7, 1), (151, 1), (8101, 1)]⟩, ⟨24917, 2, [(2, 2), (6229, 1)]⟩,
    ⟨67, 2, [(2, 1), (3, 1), (11, 1)]⟩, ⟨977, 3, [(2, 4), (61, 1)]⟩, ⟨1151, 17, [(2, 1), (5, 2), (23, 1)]⟩,
    ⟨421987, 2, [(2, 1), (3, 1), (53, 1), (1327, 1)]⟩, ⟨125803, 3, [(2, 1), (3, 2), (29, 1), (241, 1)]⟩, ⟨947, 2, [(2, 1), (11, 1), (43, 1)]⟩,
    ⟨1453, 2, [(2, 2), (3, 1), (11, 2)]⟩, ⟨1087, 3, [(2, 1), (3, 1), (181, 1)]⟩, ⟨463, 3, [(2, 1), (3, 1), (7, 1), (11, 1)]⟩,
    ⟨1709, 3, [(2, 2), (7, 1), (61, 1)]⟩, ⟨24859, 2, [(2, 1), (3, 2), (1381, 1)]⟩, ⟨859267, 2, [(2, 1), (3, 2), (47737, 1)]⟩,
    ⟨906349, 2, [(2, 2), (3, 1), (47, 1), (1607, 1)]⟩, ⟨2529403, 2, [(2, 1), (3, 1), (23, 1), (18329, 1)]⟩,
    ⟨52437899, 2, [(2, 1), (43, 1), (609743, 1)]⟩, ⟨14923, 2, [(2, 1), (3, 2), (829, 1)]⟩, ⟨4229279, 13, [(2, 1), (827, 1), (2557, 1)]⟩,
    ⟨399082391, 7, [(2, 1), (5, 1), (7, 1), (5701177, 1)]⟩, ⟨20921, 3, [(2, 3), (5, 1), (523, 1)]⟩,
    ⟨475709467, 2, [(2, 1), (3, 1), (47, 1), (1686913, 1)]⟩, ⟨772231, 6, [(2, 1), (3, 1), (5, 1), (25741, 1)]⟩, ⟨359, 7, [(2, 1), (179, 1)]⟩,
    ⟨12149, 2, [(2, 2), (3037, 1)]⟩, ⟨16447, 3, [(2, 1), (3, 1), (2741, 1)]⟩, ⟨43670061551, 7, [(2, 1), (5, 2), (17, 1), (51376543, 1)]⟩,
    ⟨149503, 3, [(2, 1), (3, 1), (24917, 1)]⟩, ⟨269, 2, [(2, 2), (67, 1)]⟩, ⟨6942563, 2, [(2, 1), (11, 1), (17, 1), (19, 1), (977, 1)]⟩,
    ⟨110573, 3, [(2, 2), (7, 1), (11, 1), (359, 1)]⟩, ⟨755057, 3, [(2, 4), (41, 1), (1151, 1)]⟩,
    ⟨13090036741, 10, [(2, 2), (3, 1), (5, 1), (11, 1), (47, 1), (421987, 1)]⟩, ⟨2012849, 3, [(2, 4), (125803, 1)]⟩, ⟨7577, 3, [(2, 3), (947, 1)]⟩,
    ⟨43591, 11, [(2, 1), (3, 1), (5, 1), (1453, 1)]⟩, ⟨4349, 2, [(2, 2), (1087, 1)]⟩, ⟨125527, 5, [(2, 1), (3, 1), (20921, 1)]⟩,
    ⟨325086459374267, 2, [(2, 1), (509, 1), (413527, 1), (772231, 1)]⟩, ⟨4129989133, 5, [(2, 2), (3, 1), (359, 1), (958679, 1)]⟩,
    ⟨5239247429827, 2, [(2, 1), (3, 2), (757, 1), (12149, 1), (31649, 1)]⟩, ⟨897019, 2, [(2, 1), (3, 1), (149503, 1)]⟩,
    ⟨3767, 5, [(2, 1), (7, 1), (269, 1)]⟩, ⟨41655379, 2, [(2, 1), (3, 1), (6942563, 1)]⟩, ⟨2653753, 5, [(2, 3), (3, 1), (110573, 1)]⟩,
    ⟨3819663927398918131021, 6, [(2, 2), (3, 2), (5, 1), (19, 1), (113, 1), (755057, 1), (13090036741, 1)]⟩, ⟨4025699, 2, [(2, 1), (2012849, 1)]⟩,
    ⟨927093389, 3, [(2, 2), (13, 1), (409, 1), (43591, 1)]⟩, ⟨582767, 5, [(2, 1), (67, 1), (4349, 1)]⟩,
    ⟨10427374428728808478656897599072717, 2, [(2, 2), (294793, 1), (4229279, 1), (399082391, 1), (5239247429827, 1)]⟩,
    ⟨417677162933, 2, [(2, 2), (59, 1), (1973, 1), (897019, 1)]⟩, ⟨1197907, 3, [(2, 1), (3, 1), (53, 1), (3767, 1)]⟩,
    ⟨22160661629, 3, [(2, 2), (7, 1), (19, 1), (41655379, 1)]⟩, ⟨63690073, 7, [(2, 3), (3, 1), (2653753, 1)]⟩,
    ⟨1125266252156850182658904441386709967, 5, [(2, 1), (3373, 1), (43670061551, 1), (3819663927398918131021, 1)]⟩,
    ⟨80513981, 2, [(2, 2), (5, 1), (4025699, 1)]⟩, ⟨64881703735777, 5, [(2, 5), (3, 7), (927093389, 1)]⟩,
    ⟨9272813673901, 2, [(2, 2), (3, 1), (5, 2), (7, 1), (7577, 1), (582767, 1)]⟩,
    ⟨539204044132271846773, 5, [(2, 2), (3, 5), (89, 1), (14923, 1), (417677162933, 1)]⟩,
    ⟨8999194758858563409123804352480028797519453, 2, [(2, 2), (3, 4), (11, 1), (2531, 1), (115603, 1), (1197907, 1), (22160661629, 1), (325086459374267, 1)]⟩,
    ⟨254760293, 2, [(2, 2), (63690073, 1)]⟩, ⟨5247740253619, 2, [(2, 1), (3, 3), (17, 1), (71, 1), (80513981, 1)]⟩,
    ⟨92691255082156974996979, 3, [(2, 1), (3, 1), (31, 1), (467, 1), (16447, 1), (64881703735777, 1)]⟩,
    ⟨1928745244171409, 3, [(2, 4), (13, 1), (9272813673901, 1)]⟩,
    ⟨28948022309329048855892746252171976963363056481941560715954676764349967630337, 5, [(2, 32), (3, 1), (463, 1), (539204044132271846773, 1), (8999194758858563409123804352480028797519453, 1)]⟩,
    ⟨52435875175126190479447740508185965837690552500527637822603658699938581184513, 7, [(2, 32), (3, 1), (11, 1), (19, 1), (10177, 1), (125527, 1), (859267, 1), (906349, 2), (2508409, 1), (2529403, 1), (52437899, 1), (254760293, 2)]⟩,
    ⟨1690502597179744445941507, 2, [(2, 1), (3, 1), (13, 1), (4129989133, 1), (5247740253619, 1)]⟩,
    ⟨15778400344354997994418419698270088123916926905054652752758194827714659, 2, [(2, 1), (3, 1), (53, 1), (475709467, 1), (92691255082156974996979, 1), (1125266252156850182658904441386709967, 1)]⟩,
    ⟨7259797099061183477, 2, [(2, 2), (941, 1), (1928745244171409, 1)]⟩,
    ⟨28948022309329048855892746252171976963363056481941647379679742748393362948097, 5, [(2, 32), (3, 2), (1709, 1), (24859, 1), (1690502597179744445941507, 1), (10427374428728808478656897599072717, 1)]⟩,
    ⟨2584487767265781317813, 2, [(2, 2), (89, 1), (7259797099061183477, 1)]⟩,
    ⟨4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787, 2, [(2, 1), (3, 2), (11, 1), (23, 1), (47, 1), (10177, 1), (859267, 1), (52437899, 1), (2584487767265781317813, 1), (15778400344354997994418419698270088123916926905054652752758194827714659, 1)]⟩ ]

private theorem isPrimeMod_two : IsPrimeMod 2 :=
  ⟨by decide, fun d hd => by have := Nat.pos_of_dvd_of_pos hd (by decide); have := Nat.le_of_dvd (by decide) hd; omega⟩

private theorem isPrimeMod_three : IsPrimeMod 3 :=
  ⟨by decide, fun d hd => by
    have := Nat.pos_of_dvd_of_pos hd (by decide); have := Nat.le_of_dvd (by decide) hd
    if hd2 : d = 2 then subst hd2; obtain ⟨k, hk⟩ := hd; omega else omega⟩

private theorem prattCerts_valid : checkPrattDAG [2, 3] prattCerts = true := by decide +kernel
private def certifiedPrimeValues : List Nat := prattCerts.map PrattCert.n

private theorem mem_certifiedPrimeValues_prime {p : Nat} (hMem : p ∈ certifiedPrimeValues) : IsPrimeMod p := by
  obtain ⟨c, hcMem, rfl⟩ := List.mem_map.1 hMem
  refine checkPrattDAG_sound prattCerts [2, 3] (fun q hq => ?_) prattCerts_valid c hcMem
  cases hq with
  | head => exact isPrimeMod_two
  | tail _ hTail => cases hTail with | head => exact isPrimeMod_three | tail _ hNil => nomatch hNil

theorem p_pallas_isPrime : IsPrimeMod p_pallas := mem_certifiedPrimeValues_prime (by decide)
theorem q_pallas_isPrime : IsPrimeMod q_pallas := mem_certifiedPrimeValues_prime (by decide)
theorem r_bls381_isPrime : IsPrimeMod r_bls381 := mem_certifiedPrimeValues_prime (by decide)
theorem p_bls381_isPrime : IsPrimeMod p_bls381 := mem_certifiedPrimeValues_prime (by decide)

theorem pallas_and_bls381_moduli_prime :
    IsPrimeMod p_pallas ∧ IsPrimeMod q_pallas ∧ IsPrimeMod p_bls381 ∧ IsPrimeMod r_bls381 :=
  ⟨p_pallas_isPrime, q_pallas_isPrime, p_bls381_isPrime, r_bls381_isPrime⟩

/-! ## 3. Projective RCB Addition Program, Curve Membership & Evaluation at the Scalar Moduli

`rcbSmul p b3 P k` is a fuelled double-and-add program over the Renes–Costello–Batina addition
formulas, computed with residues mod `p`. The two theorems below are kernel evaluations of that
program: at `k = q_pallas` (resp. `r_bls381`) its output is a projective representative of the
point at infinity, and at `k - 1` it represents `-G`. They are statements about `rcbSmul`. No
theorem here identifies `rcbSmul` with scalar multiplication in the curve group (correctness of
the formulas, associativity), so "`G` has prime order `q`" is not a theorem of this file; it
follows from these evaluations and `q_pallas_isPrime` / `r_bls381_isPrime` only once that bridge
is proved. -/

structure RcbProjPoint where
  x : Nat
  y : Nat
  z : Nat
  deriving DecidableEq, Repr

private def strictNatP (n : Nat) (k : Nat → RcbProjPoint) : RcbProjPoint :=
  match n with | 0 => k 0 | m + 1 => k (m + 1)
private def mkStrictPoint (x y z : Nat) : RcbProjPoint :=
  strictNatP x fun vx => strictNatP y fun vy => strictNatP z fun vz => ⟨vx, vy, vz⟩

def toRcbProj : SwPoint → RcbProjPoint | none => ⟨0, 1, 0⟩ | some (x, y) => ⟨x, y, 1⟩
def isProjIdentity (p : Nat) (P : RcbProjPoint) : Bool := (P.x % p == 0) && (P.y % p != 0) && (P.z % p == 0)
def projEqAffine (p : Nat) (P : RcbProjPoint) : SwPoint → Bool
  | none => isProjIdentity p P
  | some (ax, ay) => (P.z % p != 0) && ((P.x % p) == (ax * P.z) % p) && ((P.y % p) == (ay * P.z) % p)

/-- Eagerly reduced Renes–Costello–Batina (2016) Algorithm 7 complete addition for `a = 0`, `b3 = 3 * b`. -/
def rcbAdd (p b3 : Nat) (P Q : RcbProjPoint) : RcbProjPoint :=
  let addM := fun u v => (u + v) % p; let subM := fun u v => (u + p - (v % p)) % p; let mulM := fun u v => (u * v) % p
  strictNatP (mulM P.x Q.x) fun t0 => strictNatP (mulM P.y Q.y) fun t1 => strictNatP (mulM P.z Q.z) fun zz =>
  strictNatP (subM (mulM (addM P.x P.y) (addM Q.x Q.y)) (addM t0 t1)) fun t3 =>
  strictNatP (subM (mulM (addM P.y P.z) (addM Q.y Q.z)) (addM t1 zz)) fun t4 =>
  strictNatP (subM (mulM (addM P.x P.z) (addM Q.x Q.z)) (addM t0 zz)) fun y30 =>
  strictNatP ((3 * t0) % p) fun t03 => strictNatP (mulM b3 zz) fun t2 =>
  strictNatP (addM t1 t2) fun z30 => strictNatP (subM t1 t2) fun t1s => strictNatP (mulM b3 y30) fun cross =>
  mkStrictPoint (subM (mulM t3 t1s) (mulM t4 cross)) (addM (mulM t1s z30) (mulM cross t03))
    (addM (mulM z30 t4) (mulM t03 t3))

def rcbSmulFuel (p b3 : Nat) (base : RcbProjPoint) : Nat → Nat → RcbProjPoint
  | 0, _ => ⟨0, 1, 0⟩
  | fuel + 1, k =>
    if k = 0 then ⟨0, 1, 0⟩
    else let half := rcbSmulFuel p b3 base fuel (k / 2); let dbl := rcbAdd p b3 half half
         if k % 2 = 1 then rcbAdd p b3 dbl base else dbl

def rcbSmul (p b3 : Nat) (base : RcbProjPoint) (k : Nat) : RcbProjPoint := rcbSmulFuel p b3 base 256 k

/-- `orchardSpendAuthG` and `pastaPallasG` satisfy the Pallas curve equation; the program `rcbSmul`
    run on each with scalar `q_pallas` returns a projective identity representative; and run on
    `orchardSpendAuthG` with `q_pallas - 1` it returns a representative of `-orchardSpendAuthG`.
    A computation of `rcbSmul`, not a statement about the order of the points in the curve group. -/
theorem orchardSpendAuthG_onCurve_and_prime_subgroup_order :
    pallasCurve.onCurve orchardSpendAuthG = true ∧ pallasCurve.onCurve pastaPallasG = true ∧
    isProjIdentity p_pallas (rcbSmul p_pallas 15 (toRcbProj orchardSpendAuthG) q_pallas) = true ∧
    isProjIdentity p_pallas (rcbSmul p_pallas 15 (toRcbProj pastaPallasG) q_pallas) = true ∧
    projEqAffine p_pallas (rcbSmul p_pallas 15 (toRcbProj orchardSpendAuthG) (q_pallas - 1))
      (pallasCurve.neg orchardSpendAuthG) = true :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- `bls381G1` satisfies the BLS12-381 `G_1` curve equation; `rcbSmul` run on it with scalar
    `r_bls381` returns a projective identity representative, and with `r_bls381 - 1` a
    representative of `-bls381G1`. A computation of `rcbSmul`, not a statement about the order
    of `bls381G1` in the curve group. -/
theorem bls381G1_onCurve_and_prime_subgroup_order :
    bls381Curve.onCurve bls381G1 = true ∧
    isProjIdentity p_bls381 (rcbSmul p_bls381 12 (toRcbProj bls381G1) r_bls381) = true ∧
    projEqAffine p_bls381 (rcbSmul p_bls381 12 (toRcbProj bls381G1) (r_bls381 - 1))
      (bls381Curve.neg bls381G1) = true :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem projEqAffine_zk_constraint_sound {p ax ay : Nat} {P : RcbProjPoint} {zInv : Nat}
    (hAx : ax < p) (hAy : ay < p) (hZInv : (P.z * zInv) % p = 1)
    (hX : P.x % p = (ax * P.z) % p) (hY : P.y % p = (ay * P.z) % p) :
    P.z % p ≠ 0 ∧ (P.x * zInv) % p = ax ∧ (P.y * zInv) % p = ay := by
  have hZNe : P.z % p ≠ 0 := fun hz0 => by
    have : (P.z * zInv) % p = 0 := by rw [Nat.mul_mod, hz0, Nat.zero_mul, Nat.zero_mod]
    omega
  have hCoord : ∀ {coord aff : Nat}, aff < p → coord % p = (aff * P.z) % p → (coord * zInv) % p = aff := by
    intro coord aff hLt hEq
    calc (coord * zInv) % p = (((aff * P.z) % p) * (zInv % p)) % p := by rw [Nat.mul_mod, hEq]
      _ = (aff * (P.z * zInv)) % p := by rw [← Nat.mul_mod, Nat.mul_assoc]
      _ = ((aff % p) * 1) % p := by rw [Nat.mul_mod, hZInv]
      _ = aff := by rw [Nat.mul_one, Nat.mod_mod, Nat.mod_eq_of_lt hLt]
  exact ⟨hZNe, hCoord hAx hX, hCoord hAy hY⟩


/-! ### Exports for lane cred-mig -/

theorem NULLIFIER_DOMAIN_eq : NULLIFIER_DOMAIN = 0x4d49475f4e554c31 := by rfl

theorem ScalarGroup.nullifierTag_injective {g₁ g₂ : ScalarGroup}
    (h : g₁.nullifierTag = g₂.nullifierTag) : g₁ = g₂ := by
  cases g₁ <;> cases g₂ <;> first | rfl | (exact absurd (congrArg Goldilocks.val h) (by decide))

end Qsag

/-! ### Exports for lane math -/
public section

#verify_constructive Qsag.TaprootCurveProjection.compressed_injective
#verify_constructive Qsag.taproot_even_y_parity_restores_canonical_injectivity
#verify_constructive Qsag.slip0010_ed25519_clamped_canonical_nonzero
#verify_constructive Qsag.checkPrattStep_sound
#verify_constructive Qsag.bls381G1_onCurve_and_prime_subgroup_order

end
