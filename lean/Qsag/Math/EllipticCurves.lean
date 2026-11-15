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

/-- Exact `secp256k1` prime subgroup order `SECP_N` (`secp256k1_ct.rs:19-24`). -/
@[expose] def SECP256K1_ORDER_N : Nat :=
  0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141

/-- Exact `Ed25519` prime subgroup order `ED_ORDER` (`scalar.rs:8-13`). -/
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
    curve, with `n` and `p` odd. `smul_add` is the homomorphism law of the cyclic subgroup;
    with `order` and `exact` it gives `[n - s]G = -[s]G` and injectivity on `[0, n)`.
    None of the five group fields is derived here from the addition formulas. -/
structure Curve.PrimeOrderGroup (C : Curve) (G : Point) (n : Nat) : Prop where
  p_prime  : IsPrime C.p
  p_odd    : C.p % 2 = 1
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

/-- The generator `(2, 12)` of `y² = x³ + 7` over `ℤ/43` has exact order `31`, and
    all seven `PrimeOrderGroup` facts hold; the group table is checked by the kernel. -/
theorem secp7Mod43_group : secp7Mod43.PrimeOrderGroup secp7Mod43G 31 where
  p_prime := prime43
  p_odd := by decide
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
`p` and `n` odd, `p ≡ 3 (mod 4)`, `a = 0`, `b = 7`, and `G` on the curve. Not checked:
primality of `p` and the four group facts of `PrimeOrderGroup` for `G` (closure of its
multiples, the homomorphism law, `[n]G = O`, exact order). They are the hypothesis
`Secp256k1GroupLaws`; SEC 2 v2.0 §2.4.1 states them for these parameters. -/

/-- `secp256k1` field prime `p = 2^256 - 2^32 - 977` (`secp256k1_ct.rs:8-13`). -/
def SECP256K1_FIELD_P : Nat :=
  0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F

