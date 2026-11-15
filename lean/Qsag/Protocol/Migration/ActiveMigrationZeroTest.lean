module
/-
# Migration algebra, executable check boundaries, and settlement

The historical scalar-residue and tower-field models below are algebraic test
models. Their public keys reveal their scalars; their packed field words are NOT
Rust's polynomial basis. Their ideal machines and masking lemmas do not establish
production curve refinement, active-MPC security, or full-execution privacy.
Existing declaration names are retained for source compatibility.

`MigrationExecution` below separates the Rust polynomial-basis arithmetic from
that tower model, consumes multiplication results in a linked circuit trace,
checks the actual witness lane words, and carries a spent-nullifier ledger across
turns. Its exact gate checker is a reference checker, not Rust's recursive
BBCGGI19 protocol.

The Rust polynomial basis is proved a commutative ring without zero divisors,
isomorphic to `Tower128` by `rustToTower` (Horner evaluation at a tower root of
`x^128 + x^7 + x^2 + x + 1`). On that field the recursive inner-product
sacrifice is modelled from its first inner-product claim: for a false claim and
any adaptive prover, at most `sacrificeBadCoinBound` of the `|S|^r * |Sb|` coin
vectors accept (`recursive_sacrifice_false_claim_accepting_coins_bound`).

`Weierstrass` gives affine short-Weierstrass arithmetic over `ℤ/p` and derives the
Taproot x-only / y-parity laws for the points `[s]G` from the group facts
`Curve.PrimeOrderGroup`. Those facts are proved for `y² = x³ + 7` over `ℤ/43`
and are the hypothesis `Weierstrass.Secp256k1GroupLaws` for secp256k1.

The two lockstep instances and 64 lanes of one flush, and the seven engine
forks covering 438 repetitions, are composed in
`flush_false_lane_accepting_coins_bound` and
`migration_ceremony_false_repetition_below_2_pow_neg_246`.

Outstanding production refinements: the secp256k1 group facts above and all of
Ed25519, the circuit's windowed scalar multiplication, concrete address hashes
and nullifier sponge, the prime-field checks of the same flush,
the coin-flip/PRSS transport of the sacrifice, and simulation of the entire
adversarial execution. The circuit-to-`PendingAnd` fault link and the batching
of Boolean `AND` gates into the first inner-product claims (`γ` combiner and
degree-30 round 0, `BIT_CHECK_DEGREE = 54`) are proved in §11 below.
-/

public import Qsag.Math.Constructive
public import Qsag.Math.BinaryTower
public import Qsag.Exec.SimulationSpine
public import Qsag.Oracle.UcGames
public import Qsag.Tactic.AssuranceKit

public section

namespace Qsag

set_option autoImplicit false

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

/-- Dropping the parity bit loses injectivity at every order above two: `[1]G` and
    `[n - 1]G` are distinct multiples with one `x`-coordinate. -/
theorem TaprootCurveProjection.tooth_xonly_not_injective {n : Nat} {XCoord : Type}
    (proj : TaprootCurveProjection n XCoord) (hn : 2 < n) :
    ∃ s1 s2, 0 < s1 ∧ s1 < n ∧ 0 < s2 ∧ s2 < n ∧ s1 ≠ s2 ∧ proj.xOf s1 = proj.xOf s2 :=
  ⟨1, n - 1, by omega, by omega, by omega, by omega, by omega,
    (proj.sameX_iff 1 (n - 1) (by omega) (by omega) (by omega) (by omega)).mpr (Or.inr rfl)⟩

#tooth_pair
  Qsag.TaprootCurveProjection.compressed_injective
  vs
  Qsag.TaprootCurveProjection.tooth_xonly_not_injective

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

/-- **`#tooth` Taproot `x`-Only Non-Injectivity Without `y[0]` Parity**: without
    `ownership.rs:282` (`c.output(y[0])`), `proj.xOf` is not injective on the canonical
    `secp256k1` scalars `[1, SECP_N - 1]`: `1#256` and `secpNegScalar 1#256` are distinct
    canonical scalars sharing one `x`-coordinate. -/
theorem tooth_taproot_xonly_not_injective_without_y_parity
    {XCoord : Type} (proj : TaprootCurveProjection SECP256K1_ORDER_N XCoord) :
    ∃ s1 s2 : BitVec 256,
      requireCanonicalScalar .Secp256k1 s1 = true ∧
      requireCanonicalScalar .Secp256k1 s2 = true ∧
      s1 ≠ s2 ∧
      taprootXOnlySameX s1 s2 ∧
      proj.xOf s1.toNat = proj.xOf s2.toNat := by
  have h1Canon : requireCanonicalScalar .Secp256k1 1#256 = true := by
    unfold requireCanonicalScalar ScalarGroup.orderNat SECP256K1_ORDER_N
    decide
  obtain ⟨_, h2Canon, _, hNe, hSameX⟩ := secpNegScalar_props h1Canon
  exact ⟨1#256, secpNegScalar 1#256, h1Canon, h2Canon, hNe, hSameX,
    (proj.sameX_iff_canonical 1#256 (secpNegScalar 1#256) h1Canon h2Canon).mpr hSameX⟩

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

#tooth_pair
  Qsag.taproot_even_y_parity_restores_canonical_injectivity
  vs
  Qsag.tooth_taproot_xonly_not_injective_without_y_parity

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

/-- Primality as a divisor statement (Euclid, *Elements* VII, Def. 11). -/
def IsPrime (p : Nat) : Prop := 2 ≤ p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p

/-- Euclid's lemma (*Elements* VII.30). -/
theorem IsPrime.dvd_mul {p a b : Nat} (hp : IsPrime p) (h : p ∣ a * b) : p ∣ a ∨ p ∣ b := by
  rcases hp.2 (Nat.gcd p a) (Nat.gcd_dvd_left p a) with h1 | hpg
  · exact Or.inr (Nat.Coprime.dvd_of_dvd_mul_left h1 h)
  · have hd := Nat.gcd_dvd_right p a
    rw [hpg] at hd
    exact Or.inl hd

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

/-- A point of order two keeps its parity under negation: on `y² = x³ + 7` over `ℤ/7`
    the point `(0, 0)` is its own negative. `PrimeOrderGroup.n_odd` excludes this. -/
theorem tooth_two_torsion_point_is_its_own_negative :
    ∃ (C : Curve) (P : Point), C.OnCurve P ∧ P ≠ none ∧ C.p % 2 = 1 ∧
      Point.yOdd (C.neg P) = Point.yOdd P ∧ C.smul 2 P = none := by
  refine ⟨⟨7, 0, 7⟩, some (0, 0), ?_, ?_, ?_, ?_, ?_⟩ <;> decide

#tooth_pair
  Qsag.Weierstrass.Curve.PrimeOrderGroup.xonly_parity_laws
  vs
  Qsag.Weierstrass.tooth_two_torsion_point_is_its_own_negative

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

/-- The unproved group facts for the `secp256k1` generator: `p` prime, every multiple
    of `G` on the curve, `[a + b]G = [a]G + [b]G`, `[n]G = O`, and `[k]G ≠ O` for
    `0 < k < n`. The two parity fields are proved in `secp256k1_checked_parameters`. -/
abbrev Secp256k1GroupLaws : Prop :=
  secp256k1Curve.PrimeOrderGroup secp256k1G SECP256K1_ORDER_N

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

/-- **`#tooth` Ed25519 Clamped Scalars Exceed `ED_ORDER` & Wrap Non-Injectively (`tooth_ed25519_clamped_wraps_mod_order_non_injective`)**:
    1. Every clamped value `c = clampEd25519Bytes32 raw` satisfies `ED25519_ORDER_L < c.toNat`, so
       feeding `c` directly into `requireCanonicalScalar .Ed25519` **always fails** (`= false`), and
       `reduceEd25519Order c ≠ c`.
    2. Distinct values `≥ ED_ORDER` (`x1 = BitVec.ofNat 256 (2^254)` and
       `x2 = BitVec.ofNat 256 (2^254 - ED25519_ORDER_L)`, both `> ED25519_ORDER_L`) wrap to the
       **same** canonical scalar modulo `ED_ORDER`, proving `reduceEd25519Order`,
       `clampEd25519Bytes32`, and `normalizeSlip0010Ed25519Scalar` are all non-injective! -/
theorem tooth_ed25519_clamped_wraps_mod_order_non_injective :
    ∃ x1 x2 : BitVec 256,
      (∀ raw : BitVec 256,
        ED25519_ORDER_L < (clampEd25519Bytes32 raw).toNat ∧
        requireCanonicalScalar .Ed25519 (clampEd25519Bytes32 raw) = false ∧
        reduceEd25519Order (clampEd25519Bytes32 raw) ≠ clampEd25519Bytes32 raw) ∧
      ED25519_ORDER_L ≤ x1.toNat ∧
      ED25519_ORDER_L ≤ x2.toNat ∧
      x1 ≠ x2 ∧
      reduceEd25519Order x1 = reduceEd25519Order x2 ∧
      ¬ Function.Injective clampEd25519Bytes32 ∧
      ¬ Function.Injective reduceEd25519Order ∧
      ¬ Function.Injective normalizeSlip0010Ed25519Scalar := by
  have hOrd := curve_orders_match_le_limbs_and_bounds
  have hOrdLt253 : ED25519_ORDER_L < 2 ^ 253 := hOrd.2.2.2.2.2.2.1
  have h253_254 : (2 : Nat) ^ 254 = 2 * (2 ^ 253) := by decide
  have h254Lt256 : (2 : Nat) ^ 254 < 2 ^ 256 := by decide
  have hAllWrap : ∀ raw : BitVec 256,
      ED25519_ORDER_L < (clampEd25519Bytes32 raw).toNat ∧
      requireCanonicalScalar .Ed25519 (clampEd25519Bytes32 raw) = false ∧
      reduceEd25519Order (clampEd25519Bytes32 raw) ≠ clampEd25519Bytes32 raw := by
    intro raw
    have hb := clampEd25519Bytes32_bits_and_range raw
    have hGtOrd : ED25519_ORDER_L < (clampEd25519Bytes32 raw).toNat := by omega
    have hNotCanon : requireCanonicalScalar .Ed25519 (clampEd25519Bytes32 raw) = false := by
      unfold requireCanonicalScalar ScalarGroup.orderNat
      have hNotLt : ¬ ((clampEd25519Bytes32 raw).toNat < ED25519_ORDER_L) := by omega
      rw [decide_eq_false hNotLt, Bool.and_false]
    have hRedNe : reduceEd25519Order (clampEd25519Bytes32 raw) ≠ clampEd25519Bytes32 raw := by
      intro hEq
      have hv := congrArg BitVec.toNat hEq
      unfold reduceEd25519Order at hv
      have hModLt : (clampEd25519Bytes32 raw).toNat % ED25519_ORDER_L < ED25519_ORDER_L :=
        Nat.mod_lt _ (by omega)
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hv
      omega
    exact ⟨hGtOrd, hNotCanon, hRedNe⟩
  let x1 : BitVec 256 := clampEd25519Bytes32 0#256
  let x2 : BitVec 256 := BitVec.ofNat 256 (x1.toNat - ED25519_ORDER_L)
  have hx1Val : x1.toNat = 2 ^ 254 := by
    change clampEd25519Nat 0 = 2 ^ 254
    unfold clampEd25519Nat
    simp
  have hx2Val : x2.toNat = 2 ^ 254 - ED25519_ORDER_L := by
    dsimp [x2]
    rw [hx1Val, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hx1Ge : ED25519_ORDER_L ≤ x1.toNat := by omega
  have hx2Ge : ED25519_ORDER_L ≤ x2.toNat := by omega
  have hx1NeX2 : x1 ≠ x2 := by
    intro hEq
    have hv := congrArg BitVec.toNat hEq
    omega
  have hRedEq : reduceEd25519Order x1 = reduceEd25519Order x2 := by
    unfold reduceEd25519Order
    apply congrArg (BitVec.ofNat 256)
    rw [hx1Val, hx2Val]
    have hSplit : 2 ^ 254 = (2 ^ 254 - ED25519_ORDER_L) + ED25519_ORDER_L * 1 := by omega
    conv => lhs; rw [hSplit]
    rw [Nat.add_mul_mod_self_left]
  have hClamp01 : clampEd25519Bytes32 0#256 = clampEd25519Bytes32 1#256 := by
    apply BitVec.eq_of_toNat_eq
    change clampEd25519Nat 0 = clampEd25519Nat 1
    unfold clampEd25519Nat
    have h1Mod : 1 % (2 ^ 254) = 1 := Nat.mod_eq_of_lt (by decide)
    rw [h1Mod]
  have h0Ne1 : (0#256 : BitVec 256) ≠ 1#256 := by decide
  exact ⟨x1, x2, hAllWrap, hx1Ge, hx2Ge, hx1NeX2, hRedEq,
    fun hInj => h0Ne1 (hInj hClamp01),
    fun hInj => hx1NeX2 (hInj hRedEq),
    fun hInj => h0Ne1 (hInj (congrArg reduceEd25519Order hClamp01))⟩

#tooth_pair
  Qsag.slip0010_ed25519_clamped_canonical_nonzero
  vs
  Qsag.tooth_ed25519_clamped_wraps_mod_order_non_injective

/-! ## 2. Canonical Subgroup `ScalarPointHom`, Shor Pre-Migration Boundary & Premature-Open `#tooth` -/

/-- Recursive little-endian bit packer producing `< 2^w` naturals from `Nat → Bool`. -/
def packBitsAux : Nat → (Nat → Bool) → Nat
  | 0, _ => 0
  | k + 1, f => (if f 0 then 1 else 0) + 2 * packBitsAux k (fun j => f (j + 1))

theorem packBitsAux_lt : ∀ (w : Nat) (f : Nat → Bool), packBitsAux w f < 2 ^ w
  | 0, _ => by simp [packBitsAux]
  | k + 1, f => by
    have ih := packBitsAux_lt k (fun j => f (j + 1))
    simp only [packBitsAux, Nat.pow_succ]
    cases f 0 <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

theorem packBitsAux_testBit : ∀ (w : Nat) (f : Nat → Bool) (i : Nat),
    (packBitsAux w f).testBit i = (decide (i < w) && f i)
  | 0, _, i => by simp [packBitsAux]
  | k + 1, f, 0 => by
    simp only [packBitsAux, Nat.testBit_zero, Nat.zero_lt_succ, decide_true, Bool.true_and]
    cases f 0 <;> simp [Nat.add_mul_mod_self_left]
  | k + 1, f, j + 1 => by
    simp only [packBitsAux, Nat.testBit_succ, Nat.succ_lt_succ_iff]
    have hDiv : ((if f 0 then 1 else 0) + 2 * packBitsAux k (fun r => f (r + 1))) / 2 =
        packBitsAux k (fun r => f (r + 1)) := by
      cases f 0 <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
    rw [hDiv, packBitsAux_testBit k (fun r => f (r + 1)) j]

/-- Pack `w` Boolean bits into a `BitVec w` with `(packBits w f).getLsbD i = f i` for `i < w`. -/
def packBits (w : Nat) (f : Nat → Bool) : BitVec w :=
  BitVec.ofNatLT (packBitsAux w f) (packBitsAux_lt w f)

theorem packBits_getLsbD (w : Nat) (f : Nat → Bool) (i : Nat) (hi : i < w) :
    (packBits w f).getLsbD i = f i := by
  change (packBitsAux w f).testBit i = f i
  rw [packBitsAux_testBit, decide_eq_true hi, Bool.true_and]

/-- Single-bit fault vector `e_idx` with bit `idx` set and all other bits zero. -/
def oneBitMask (w idx : Nat) : BitVec w :=
  packBits w (fun j => decide (j = idx))

theorem oneBitMask_getLsbD (w idx j : Nat) (hj : j < w) :
    (oneBitMask w idx).getLsbD j = decide (j = idx) :=
  packBits_getLsbD w (fun r => decide (r = idx)) j hj

/-- Every odd integer `M > 1` is coprime to `2^i` (`(2^i) % M ≠ 0` for all `i : Nat`). -/
theorem odd_not_dvd_two_pow {M : Nat} (hOdd : M % 2 = 1) (hGt1 : 1 < M) :
    ∀ i : Nat, (2 ^ i) % M ≠ 0
  | 0 => by
    have h1 : 1 % M = 1 := Nat.mod_eq_of_lt hGt1
    simp [h1]
  | i + 1 => by
    intro hZero
    have ih := odd_not_dvd_two_pow hOdd hGt1 i
    rw [Nat.pow_succ, Nat.mul_comm] at hZero
    have hDivEq : M * ((2 * 2 ^ i) / M) + (2 * 2 ^ i) % M = 2 * 2 ^ i :=
      Nat.div_add_mod (2 * 2 ^ i) M
    rw [hZero, Nat.add_zero] at hDivEq
    let q := (2 * 2 ^ i) / M
    have hqEven : q % 2 = 0 := by
      have hMod2 : (M * q) % 2 = ((M % 2) * (q % 2)) % 2 := Nat.mul_mod M q 2
      have hMq : M * q = 2 * 2 ^ i := hDivEq
      rw [hMq, hOdd] at hMod2
      omega
    have hqHalf : q = 2 * (q / 2) := by omega
    have hMul2 : 2 * (M * (q / 2)) = 2 * 2 ^ i := by
      calc 2 * (M * (q / 2))
        _ = M * (2 * (q / 2)) := by rw [← Nat.mul_assoc, Nat.mul_comm 2 M, Nat.mul_assoc]
        _ = M * q := by rw [← hqHalf]
        _ = 2 * 2 ^ i := hDivEq
    have hHalfEq : 2 ^ i = M * (q / 2) := (Nat.mul_left_cancel (by decide : 0 < 2) hMul2).symm
    rw [hHalfEq, Nat.mul_mod_right] at ih
    exact ih rfl

private def modAddVal (M a b : Nat) : Nat :=
  if a + b < M then a + b else a + b - M

private def modSubVal (M a b : Nat) : Nat :=
  if b ≤ a then a - b else a + M - b

private theorem modAddVal_lt {M a b : Nat} (ha : a < M) (hb : b < M) : modAddVal M a b < M := by
  unfold modAddVal
  cases (inferInstance : Decidable (a + b < M)) with
  | isTrue h => rw [cIte_pos h]; omega
  | isFalse h => rw [cIte_neg h]; omega

private theorem modSubVal_lt {M a b : Nat} (ha : a < M) (hb : b < M) : modSubVal M a b < M := by
  unfold modSubVal
  cases (inferInstance : Decidable (b ≤ a)) with
  | isTrue h => rw [cIte_pos h]; omega
  | isFalse h => rw [cIte_neg h]; omega

private theorem modAddVal_eq_mod {M a b : Nat} (ha : a < M) (hb : b < M) :
    modAddVal M a b = (a + b) % M := by
  unfold modAddVal
  cases (inferInstance : Decidable (a + b < M)) with
  | isTrue h =>
    rw [cIte_pos h, Nat.mod_eq_of_lt h]
  | isFalse h =>
    rw [cIte_neg h]
    have hGe : M ≤ a + b := by omega
    have hSubLt : a + b - M < M := by omega
    rw [Nat.mod_eq_sub_mod hGe, Nat.mod_eq_of_lt hSubLt]

private theorem modAddVal_comm (M a b : Nat) : modAddVal M a b = modAddVal M b a := by
  unfold modAddVal; rw [Nat.add_comm a b]

private theorem modAddVal_assoc {M a b c : Nat} (ha : a < M) (hc : c < M) :
    modAddVal M (modAddVal M a b) c = modAddVal M a (modAddVal M b c) := by
  unfold modAddVal
  cases (inferInstance : Decidable (a + b < M)) with
  | isTrue hab =>
    rw [cIte_pos hab]
    cases (inferInstance : Decidable (b + c < M)) with
    | isTrue hbc =>
      rw [cIte_pos hbc]
      cases (inferInstance : Decidable (a + b + c < M)) with
      | isTrue h3 => rw [cIte_pos h3, cIte_pos (by omega : a + (b + c) < M)]; omega
      | isFalse h3 => rw [cIte_neg h3, cIte_neg (by omega : ¬ (a + (b + c) < M))]; omega
    | isFalse hbc =>
      rw [cIte_neg hbc, cIte_neg (by omega : ¬ (a + b + c < M)),
          cIte_pos (by omega : a + (b + c - M) < M)]; omega
  | isFalse hab =>
    rw [cIte_neg hab]
    cases (inferInstance : Decidable (b + c < M)) with
    | isTrue hbc =>
      rw [cIte_pos hbc, cIte_pos (by omega : a + b - M + c < M),
          cIte_neg (by omega : ¬ (a + (b + c) < M))]; omega
    | isFalse hbc =>
      rw [cIte_neg hbc]
      cases (inferInstance : Decidable (a + b - M + c < M)) with
      | isTrue h3 => rw [cIte_pos h3, cIte_pos (by omega : a + (b + c - M) < M)]; omega
      | isFalse h3 => rw [cIte_neg h3, cIte_neg (by omega : ¬ (a + (b + c - M) < M))]; omega

private theorem modAddVal_zero_left {M a : Nat} (ha : a < M) : modAddVal M 0 a = a := by
  unfold modAddVal
  rw [cIte_pos (by omega : 0 + a < M)]; omega

private theorem modSub_modAdd_cancel {M a b : Nat} (ha : a < M) :
    modSubVal M (modAddVal M a b) b = a := by
  unfold modSubVal modAddVal
  cases (inferInstance : Decidable (a + b < M)) with
  | isTrue h1 => rw [cIte_pos h1, cIte_pos (by omega : b ≤ a + b)]; omega
  | isFalse h1 => rw [cIte_neg h1, cIte_neg (by omega : ¬ (b ≤ a + b - M))]; omega

private theorem modAdd_modSub_cancel {M a b : Nat} (ha : a < M) (hb : b < M) :
    modAddVal M (modSubVal M a b) b = a := by
  unfold modAddVal modSubVal
  cases (inferInstance : Decidable (b ≤ a)) with
  | isTrue h1 => rw [cIte_pos h1, cIte_pos (by omega : a - b + b < M)]; omega
  | isFalse h1 => rw [cIte_neg h1, cIte_neg (by omega : ¬ (a + M - b + b < M))]; omega

private theorem modAdd_ne_modSub_of_odd {M p g : Nat}
    (hOdd : M % 2 = 1) (hgLt : g < M) (hgPos : 0 < g) :
    modAddVal M p g ≠ modSubVal M p g := by
  unfold modAddVal modSubVal
  cases (inferInstance : Decidable (p + g < M)) with
  | isTrue h1 =>
    rw [cIte_pos h1]
    cases (inferInstance : Decidable (g ≤ p)) with
    | isTrue h2 => rw [cIte_pos h2]; omega
    | isFalse h2 => rw [cIte_neg h2]; omega
  | isFalse h1 =>
    rw [cIte_neg h1]
    cases (inferInstance : Decidable (g ≤ p)) with
    | isTrue h2 => rw [cIte_pos h2]; omega
    | isFalse h2 => rw [cIte_neg h2]; omega

/-- Homomorphic curve-point subgroup structure (`s ↦ ∑ s_i · [2^i]G`) with non-2-torsion bit
    generators and injective point wire encoding. -/
structure ScalarPointHom (w pWidth : Nat) (PubKey : Type) [DecidableEq PubKey] where
  ptZero          : PubKey
  ptAdd           : PubKey → PubKey → PubKey
  ptSub           : PubKey → PubKey → PubKey
  genBit          : Nat → PubKey
  encodePk        : PubKey → BitVec pWidth
  decodePk        : BitVec pWidth → Option PubKey
  add_comm        : ∀ a b, ptAdd a b = ptAdd b a
  add_assoc       : ∀ a b c, ptAdd (ptAdd a b) c = ptAdd a (ptAdd b c)
  zero_add        : ∀ a, ptAdd ptZero a = a
  add_sub_cancel  : ∀ a b, ptSub (ptAdd a b) b = a
  sub_add_cancel  : ∀ a b, ptAdd (ptSub a b) b = a
  non_two_torsion : ∀ i, i < w → ∀ p, ptAdd p (genBit i) ≠ ptSub p (genBit i)
  decode_encode   : ∀ p, decodePk (encodePk p) = some p

theorem ScalarPointHom.encodePk_injective {w pWidth : Nat} {PubKey : Type} [DecidableEq PubKey]
    (G : ScalarPointHom w pWidth PubKey) : Function.Injective G.encodePk := by
  intro a b hEq
  have hDec : G.decodePk (G.encodePk a) = G.decodePk (G.encodePk b) := congrArg G.decodePk hEq
  rw [G.decode_encode, G.decode_encode] at hDec
  injection hDec

/-- Prefix binary scalar multiplication `∑_{j < k, s[j]=1} genBit j`. -/
def scalarMulPrefix {w pWidth : Nat} {PubKey : Type} [DecidableEq PubKey]
    (G : ScalarPointHom w pWidth PubKey) (s : BitVec w) : Nat → PubKey
  | 0 => G.ptZero
  | k + 1 =>
    let prev := scalarMulPrefix G s k
    if s.getLsbD k then G.ptAdd prev (G.genBit k) else prev

/-- Full `w`-bit public-key map `pkOf(s) := scalarMulPrefix G s w`. -/
def scalarMulKey {w pWidth : Nat} {PubKey : Type} [DecidableEq PubKey]
    (G : ScalarPointHom w pWidth PubKey) (s : BitVec w) : PubKey :=
  scalarMulPrefix G s w

private theorem ptAdd_right_comm {w pWidth : Nat} {PubKey : Type} [DecidableEq PubKey]
    (G : ScalarPointHom w pWidth PubKey) (a b c : PubKey) :
    G.ptAdd (G.ptAdd a b) c = G.ptAdd (G.ptAdd a c) b := by
  rw [G.add_assoc, G.add_comm b c, ← G.add_assoc]

private theorem ptSub_ptAdd_swap {w pWidth : Nat} {PubKey : Type} [DecidableEq PubKey]
    (G : ScalarPointHom w pWidth PubKey) (a b c : PubKey) :
    G.ptAdd (G.ptSub a b) c = G.ptSub (G.ptAdd a c) b := by
  have h1 : G.ptAdd (G.ptAdd (G.ptSub a b) c) b = G.ptAdd a c := by
    rw [ptAdd_right_comm G (G.ptSub a b) c b, G.sub_add_cancel]
  have h2 := congrArg (fun u => G.ptSub u b) h1
  rw [G.add_sub_cancel] at h2
  exact h2

private theorem scalarMulPrefix_xor_oneBit_le {w pWidth : Nat} {PubKey : Type} [DecidableEq PubKey]
    (G : ScalarPointHom w pWidth PubKey) (s : BitVec w) {i : Nat} (hi : i < w) :
    ∀ k, k ≤ i → scalarMulPrefix G (s ^^^ oneBitMask w i) k = scalarMulPrefix G s k
  | 0, _ => rfl
  | k + 1, hkLe => by
    have hkLtW : k < w := by omega
    have hkNe : k ≠ i := by omega
    simp only [scalarMulPrefix, BitVec.getLsbD_xor, oneBitMask_getLsbD w i k hkLtW,
      decide_eq_false hkNe, bool_xor_false,
      scalarMulPrefix_xor_oneBit_le G s hi k (Nat.le_of_succ_le hkLe)]

private theorem scalarMulPrefix_xor_oneBit_gt {w pWidth : Nat} {PubKey : Type} [DecidableEq PubKey]
    (G : ScalarPointHom w pWidth PubKey) (s : BitVec w) {i : Nat} (hi : i < w) :
    ∀ k, i < k → k ≤ w →
      scalarMulPrefix G (s ^^^ oneBitMask w i) k =
        if s.getLsbD i then G.ptSub (scalarMulPrefix G s k) (G.genBit i)
        else G.ptAdd (scalarMulPrefix G s k) (G.genBit i)
  | 0, hGt, _ => by omega
  | k + 1, hGt, hkLe => by
    if hEq : k = i then
      subst hEq
      have hPre := scalarMulPrefix_xor_oneBit_le G s hi k (Nat.le_refl k)
      simp only [scalarMulPrefix, hPre, BitVec.getLsbD_xor, oneBitMask_getLsbD w k k hi,
        decide_true]
      cases hs : s.getLsbD k
      · simp
      · simp [G.add_sub_cancel]
    else
      have hiLtK : i < k := by omega
      have hkLtW : k < w := hkLe
      have ih := scalarMulPrefix_xor_oneBit_gt G s hi k hiLtK (Nat.le_of_succ_le hkLe)
      simp only [scalarMulPrefix, BitVec.getLsbD_xor, oneBitMask_getLsbD w i k hkLtW,
        decide_eq_false hEq, bool_xor_false, ih]
      cases hsK : s.getLsbD k <;> cases hsI : s.getLsbD i <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · exact ptAdd_right_comm G (scalarMulPrefix G s k) (G.genBit i) (G.genBit k)
      · exact ptSub_ptAdd_swap G (scalarMulPrefix G s k) (G.genBit i) (G.genBit k)

/-- **Single-Bit Fault Homomorphic Shift (`scalarMulKey_xor_oneBit`)**:
    Flipping bit `i < w` shifts `scalarMulKey G s` to `pk + genBit i` when `s[i] = 0`
    and to `pk - genBit i` when `s[i] = 1`! -/
theorem scalarMulKey_xor_oneBit {w pWidth : Nat} {PubKey : Type} [DecidableEq PubKey]
    (G : ScalarPointHom w pWidth PubKey) (s : BitVec w) {i : Nat} (hi : i < w) :
    scalarMulKey G (s ^^^ oneBitMask w i) =
      if s.getLsbD i then G.ptSub (scalarMulKey G s) (G.genBit i)
      else G.ptAdd (scalarMulKey G s) (G.genBit i) :=
  scalarMulPrefix_xor_oneBit_gt G s hi w hi (Nat.le_refl w)

/-- Transparent scalar-residue test group. The encoding reveals the discrete log.
    This is not a curve public-key implementation or a one-way function. -/
def canonicalSubgroupHom (group : ScalarGroup) :
    ScalarPointHom 256 256 (Fin group.orderNat) where
  ptZero := ⟨0, by have := (scalarGroup_order_props group).1; omega⟩
  ptAdd a b := ⟨modAddVal group.orderNat a.val b.val, modAddVal_lt a.isLt b.isLt⟩
  ptSub a b := ⟨modSubVal group.orderNat a.val b.val, modSubVal_lt a.isLt b.isLt⟩
  genBit i := ⟨(2 ^ i) % group.orderNat,
    Nat.mod_lt _ (by have := (scalarGroup_order_props group).1; omega)⟩
  encodePk p := BitVec.ofNatLT p.val (Nat.lt_trans p.isLt (scalarGroup_order_props group).2.1)
  decodePk bv := if h : bv.toNat < group.orderNat then some ⟨bv.toNat, h⟩ else none
  add_comm a b := Fin.ext (modAddVal_comm _ a.val b.val)
  add_assoc a b c := Fin.ext (modAddVal_assoc a.isLt c.isLt)
  zero_add a := Fin.ext (modAddVal_zero_left a.isLt)
  add_sub_cancel a b := Fin.ext (modSub_modAdd_cancel a.isLt)
  sub_add_cancel a b := Fin.ext (modAdd_modSub_cancel a.isLt b.isLt)
  non_two_torsion i _hi p := by
    intro hEq
    have hValEq := congrArg Fin.val hEq
    dsimp only at hValEq
    obtain ⟨hGt1, _, hOdd⟩ := scalarGroup_order_props group
    have hgNe0 : (2 ^ i) % group.orderNat ≠ 0 := odd_not_dvd_two_pow hOdd hGt1 i
    have hgLt : (2 ^ i) % group.orderNat < group.orderNat := Nat.mod_lt _ (by omega)
    exact modAdd_ne_modSub_of_odd hOdd hgLt (Nat.pos_of_ne_zero hgNe0) hValEq
  decode_encode p := by
    change (if h : p.val < group.orderNat then some ⟨p.val, h⟩ else none) = some p
    rw [cDIte_pos p.isLt]

private def prefixBitsVal {w : Nat} (s : BitVec w) : Nat → Nat
  | 0 => 0
  | k + 1 => prefixBitsVal s k + (if s.getLsbD k then 2 ^ k else 0)

private theorem prefixBitsVal_eq_mod_two_pow {w : Nat} (s : BitVec w) :
    ∀ k, k ≤ w → prefixBitsVal s k = s.toNat % (2 ^ k)
  | 0, _ => by simp [prefixBitsVal, Nat.mod_one]
  | k + 1, hkLe => by
    have ih := prefixBitsVal_eq_mod_two_pow s k (Nat.le_of_succ_le hkLe)
    simp only [prefixBitsVal, ih]
    have hBit : s.getLsbD k = s.toNat.testBit k := rfl
    rw [hBit, Nat.testBit_eq_decide_div_mod_eq]
    have hPowSucc : 2 ^ (k + 1) = 2 ^ k * 2 := Nat.pow_succ 2 k
    have hDivMod : s.toNat % (2 ^ (k + 1)) = s.toNat % (2 ^ k) + (2 ^ k) * ((s.toNat / (2 ^ k)) % 2) := by
      rw [hPowSucc]
      have h1 := Nat.div_add_mod s.toNat (2 ^ k)
      have h2 := Nat.div_add_mod (s.toNat / 2 ^ k) 2
      have h3 := Nat.div_add_mod s.toNat (2 ^ k * 2)
      have hDivDiv : s.toNat / (2 ^ k * 2) = (s.toNat / 2 ^ k) / 2 :=
        (Nat.div_div_eq_div_mul s.toNat (2 ^ k) 2).symm
      rw [hDivDiv] at h3
      have hModLt1 : s.toNat % (2 ^ k) < 2 ^ k := Nat.mod_lt _ (Nat.two_pow_pos k)
      have hModLt2 : (s.toNat / 2 ^ k) % 2 < 2 := Nat.mod_lt _ (by decide)
      have hModLt3 : s.toNat % (2 ^ k * 2) < 2 ^ k * 2 := Nat.mod_lt _ (by have := Nat.two_pow_pos k; omega)
      have hMulDist : (2 ^ k * 2) * ((s.toNat / 2 ^ k) / 2) = (2 ^ k) * (2 * ((s.toNat / 2 ^ k) / 2)) := by
        rw [Nat.mul_assoc]
      rw [hMulDist] at h3
      have hSubst : 2 * ((s.toNat / 2 ^ k) / 2) = s.toNat / 2 ^ k - (s.toNat / 2 ^ k) % 2 := by omega
      have hExpand : (2 ^ k) * (2 * ((s.toNat / 2 ^ k) / 2)) + (2 ^ k) * ((s.toNat / 2 ^ k) % 2) =
          (2 ^ k) * (s.toNat / 2 ^ k) := by
        rw [← Nat.mul_add, h2]
      omega
    rw [hDivMod]
    cases (inferInstance : Decidable ((s.toNat / 2 ^ k) % 2 = 1)) with
    | isTrue hOne =>
      rw [decide_eq_true hOne]
      simp [hOne]
    | isFalse hZero =>
      have hMod0 : (s.toNat / 2 ^ k) % 2 = 0 := by
        have := Nat.mod_lt (s.toNat / 2 ^ k) (by decide : 0 < 2)
        omega
      rw [decide_eq_false hZero]
      simp [hMod0]

private theorem scalarMulPrefix_canonical_val (group : ScalarGroup) (s : BitVec 256) :
    ∀ k, k ≤ 256 →
      (scalarMulPrefix (canonicalSubgroupHom group) s k).val =
        (prefixBitsVal s k) % group.orderNat
  | 0, _ => by simp [scalarMulPrefix, canonicalSubgroupHom, prefixBitsVal]
  | k + 1, hkLe => by
    have ih := scalarMulPrefix_canonical_val group s k (Nat.le_of_succ_le hkLe)
    obtain ⟨hGt1, _, _⟩ := scalarGroup_order_props group
    simp only [scalarMulPrefix, prefixBitsVal]
    cases hs : s.getLsbD k
    · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero, ih]
    · simp only [↓reduceIte]
      change modAddVal group.orderNat
        (scalarMulPrefix (canonicalSubgroupHom group) s k).val
        ((2 ^ k) % group.orderNat) = (prefixBitsVal s k + 2 ^ k) % group.orderNat
      rw [modAddVal_eq_mod (scalarMulPrefix (canonicalSubgroupHom group) s k).isLt
            (Nat.mod_lt _ (by omega)),
          ih, ← Nat.add_mod]

/-- Exact subgroup scalar evaluation: `scalarMulKey (canonicalSubgroupHom group) s` reduces `s.toNat`
    modulo `group.orderNat` (`SECP_N` or `ED_ORDER`). -/
theorem canonicalSubgroupHom_scalarMulKey_val (group : ScalarGroup) (s : BitVec 256) :
    (scalarMulKey (canonicalSubgroupHom group) s).val = s.toNat % group.orderNat := by
  unfold scalarMulKey
  rw [scalarMulPrefix_canonical_val group s 256 (Nat.le_refl 256),
      prefixBitsVal_eq_mod_two_pow s 256 (Nat.le_refl 256),
      Nat.mod_eq_of_lt s.isLt]

/-- **Canonical Subgroup Injectivity (`canonicalSubgroupHom_injective_on_canonical`)**:
    On `[1, group.orderNat - 1]` (`requireCanonicalScalar group s = true`), compressed / parity-pinned
    subgroup scalar multiplication `scalarMulKey (canonicalSubgroupHom group)` is strictly injective,
    whereas on unrestricted `BitVec 256` (`0#256` vs `group.orderNat`) it wraps modulo `group.orderNat`. -/
theorem canonicalSubgroupHom_injective_on_canonical (group : ScalarGroup) :
    (∀ s1 s2 : BitVec 256,
      requireCanonicalScalar group s1 = true →
      requireCanonicalScalar group s2 = true →
      scalarMulKey (canonicalSubgroupHom group) s1 =
        scalarMulKey (canonicalSubgroupHom group) s2 →
      s1 = s2) ∧
    (let sOrd := BitVec.ofNat 256 group.orderNat
     0#256 ≠ sOrd ∧
     scalarMulKey (canonicalSubgroupHom group) 0#256 =
       scalarMulKey (canonicalSubgroupHom group) sOrd) := by
  refine ⟨?_, ?_⟩
  · intro s1 s2 h1 h2 hEq
    obtain ⟨_, hLt1⟩ := (requireCanonicalScalar_iff group s1).mp h1
    obtain ⟨_, hLt2⟩ := (requireCanonicalScalar_iff group s2).mp h2
    have hv := congrArg Fin.val hEq
    rw [canonicalSubgroupHom_scalarMulKey_val, canonicalSubgroupHom_scalarMulKey_val,
        Nat.mod_eq_of_lt hLt1, Nat.mod_eq_of_lt hLt2] at hv
    exact BitVec.eq_of_toNat_eq hv
  · obtain ⟨hGt1, hLt256, _⟩ := scalarGroup_order_props group
    let sOrd := BitVec.ofNat 256 group.orderNat
    have hsOrdVal : sOrd.toNat = group.orderNat := by
      dsimp [sOrd]
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hLt256]
    refine ⟨?_, ?_⟩
    · intro hEq
      have hv := congrArg BitVec.toNat hEq
      rw [BitVec.toNat_ofNat, Nat.zero_mod, hsOrdVal] at hv
      omega
    · apply Fin.ext
      rw [canonicalSubgroupHom_scalarMulKey_val, canonicalSubgroupHom_scalarMulKey_val,
          hsOrdVal, Nat.mod_self]
      simp

/-- Historical compatibility predicate: invertibility of the transparent scalar
    test group. It models neither a quantum algorithm nor curve discrete-log hardness. -/
def ShorVulnerablePreMigration (group : ScalarGroup) : Prop :=
  ∃ shorDlog : Fin group.orderNat → BitVec 256,
    ∀ s : BitVec 256,
      requireCanonicalScalar group s = true →
      shorDlog (scalarMulKey (canonicalSubgroupHom group) s) = s

/-- Scalar-disclosure witness for the transparent test group. The inverse is
    classical and immediate; this theorem is not an implementation of Shor. -/
theorem tooth_shor_crqc_breaks_legacy_pk_pre_migration (group : ScalarGroup) :
    ∃ shorDlog : Fin group.orderNat → BitVec 256,
      ShorVulnerablePreMigration group ∧
      ∀ s : BitVec 256,
        requireCanonicalScalar group s = true →
        shorDlog (scalarMulKey (canonicalSubgroupHom group) s) = s := by
  obtain ⟨_, hLt256, _⟩ := scalarGroup_order_props group
  let shorDlog : Fin group.orderNat → BitVec 256 :=
    fun pt => BitVec.ofNatLT pt.val (Nat.lt_trans pt.isLt hLt256)
  have hInv : ∀ s : BitVec 256,
      requireCanonicalScalar group s = true →
      shorDlog (scalarMulKey (canonicalSubgroupHom group) s) = s := by
    intro s hCanon
    obtain ⟨_, hLtOrd⟩ := (requireCanonicalScalar_iff group s).mp hCanon
    apply BitVec.eq_of_toNat_eq
    change (scalarMulKey (canonicalSubgroupHom group) s).val = s.toNat
    rw [canonicalSubgroupHom_scalarMulKey_val, Nat.mod_eq_of_lt hLtOrd]
  exact ⟨shorDlog, ⟨shorDlog, hInv⟩, hInv⟩

/-- Big-endian seven-byte chunks of the 32-byte value followed by `01 00 00`,
    matching Rust `pack_bytes32_to_limbs56`. The final limb contains the delimiter. -/
def pack256ToLimbs56 (x : BitVec 256) : Fin 5 → Goldilocks :=
  fun k =>
    let slice := ((x.toNat * 2 ^ 24 + 2 ^ 16) / (2 ^ (56 * (4 - k.val)))) % (2 ^ 56)
    have hLtP : slice < goldilocksPrime := by
      have hSliceLt : slice < 2 ^ 56 := Nat.mod_lt _ (Nat.two_pow_pos 56)
      have h56LtP : (2 : Nat) ^ 56 < goldilocksPrime := by unfold goldilocksPrime; decide
      omega
    ⟨slice, hLtP⟩

theorem pack256ToLimbs56_injective {a b : BitVec 256}
    (h : pack256ToLimbs56 a = pack256ToLimbs56 b) : a = b := by
  apply BitVec.eq_of_toNat_eq
  have h0 := congrArg (fun f => (f ⟨0, by decide⟩).val) h
  have h1 := congrArg (fun f => (f ⟨1, by decide⟩).val) h
  have h2 := congrArg (fun f => (f ⟨2, by decide⟩).val) h
  have h3 := congrArg (fun f => (f ⟨3, by decide⟩).val) h
  have h4 := congrArg (fun f => (f ⟨4, by decide⟩).val) h
  simp only [pack256ToLimbs56] at h0 h1 h2 h3 h4
  have ha := a.isLt
  have hb := b.isLt
  omega

/-- The delimiter survives even for an all-zero digest. -/
theorem pack256ToLimbs56_zero_delimiter :
    (pack256ToLimbs56 (0#256) ⟨4, by decide⟩).val = 65536 := by decide

/-- Asymmetric end-byte vector catches reversed chunk order and a missing delimiter. -/
theorem pack256ToLimbs56_end_bytes :
    let x := BitVec.ofNat 256 (2 ^ 248 + 1)
    (pack256ToLimbs56 x ⟨0, by decide⟩).val = 2 ^ 48 ∧
    (pack256ToLimbs56 x ⟨4, by decide⟩).val = 2 ^ 24 + 2 ^ 16 := by decide

/-- Complete 11-limb Poseidon2 nullifier preimage matching `scalar.rs:92-100` and `ownership.rs:294-300`. -/
def migrationNullifierInput (group : ScalarGroup) (s migrationDomain : BitVec 256) :
    Fin 11 → Goldilocks :=
  fun idx =>
    if idx.val = 0 then
      group.nullifierTag
    else if h1 : idx.val < 6 then
      pack256ToLimbs56 s ⟨idx.val - 1, by omega⟩
    else
      pack256ToLimbs56 migrationDomain ⟨idx.val - 6, by omega⟩

/-- Evaluate the campaign migration nullifier under `NULLIFIER_DOMAIN = 0x4d49_475f_4e55_4c31`. -/
def computeMigrationNullifier
    (poseidon2Hash : UInt64 → (Fin 11 → Goldilocks) → (Fin 4 → Goldilocks))
    (group : ScalarGroup) (s migrationDomain : BitVec 256) : Fin 4 → Goldilocks :=
  poseidon2Hash NULLIFIER_DOMAIN (migrationNullifierInput group s migrationDomain)

/-- Nullifier preimage binding or hash collision, and destination independence.
    This compatibility theorem has no ledger and does not prove replay rejection.
    See MigrationExecution.settle_replay_rejected for the stateful property. -/
theorem post_ceremony_nullifier_domain_binding_and_replay_sound
    (poseidon2Hash : UInt64 → (Fin 11 → Goldilocks) → (Fin 4 → Goldilocks)) :
    NULLIFIER_DOMAIN = 0x4d49475f4e554c31 ∧
    (∀ (g1 g2 : ScalarGroup) (s1 s2 dom1 dom2 : BitVec 256),
      computeMigrationNullifier poseidon2Hash g1 s1 dom1 =
        computeMigrationNullifier poseidon2Hash g2 s2 dom2 →
      (g1 = g2 ∧ s1 = s2 ∧ dom1 = dom2) ∨
      (migrationNullifierInput g1 s1 dom1 ≠ migrationNullifierInput g2 s2 dom2 ∧
       poseidon2Hash NULLIFIER_DOMAIN (migrationNullifierInput g1 s1 dom1) =
         poseidon2Hash NULLIFIER_DOMAIN (migrationNullifierInput g2 s2 dom2))) ∧
    (∀ (group : ScalarGroup) (s migrationDomain pqDest1 pqDest2 : BitVec 256),
      pqDest1 ≠ pqDest2 →
      (fun _dest : BitVec 256 => computeMigrationNullifier poseidon2Hash group s migrationDomain) pqDest1 =
      (fun _dest : BitVec 256 => computeMigrationNullifier poseidon2Hash group s migrationDomain) pqDest2) := by
  refine ⟨rfl, ?_, fun _ _ _ _ _ _ => rfl⟩
  intro g1 g2 s1 s2 dom1 dom2 hNullEq
  have hInEqDec : Decidable (migrationNullifierInput g1 s1 dom1 = migrationNullifierInput g2 s2 dom2) := by
    if h0 : g1 = g2 ∧ s1 = s2 ∧ dom1 = dom2 then
      rcases h0 with ⟨rfl, rfl, rfl⟩
      exact .isTrue rfl
    else
      apply Decidable.isFalse
      intro hFunEq
      apply h0
      have hgEq : g1 = g2 := by
        have hTag := congrArg (fun f => (f ⟨0, by decide⟩).val) hFunEq
        dsimp only [migrationNullifierInput] at hTag
        cases g1 <;> cases g2 <;> simp [ScalarGroup.nullifierTag] at hTag ⊢
      have hsLimbs : pack256ToLimbs56 s1 = pack256ToLimbs56 s2 := by
        funext k
        have hk := congrArg (fun f => f ⟨k.val + 1, by omega⟩) hFunEq
        dsimp only [migrationNullifierInput] at hk
        have hNe0 : k.val + 1 ≠ 0 := by omega
        have hLt6 : k.val + 1 < 6 := by omega
        rw [cIte_neg hNe0, cDIte_pos hLt6, cIte_neg hNe0, cDIte_pos hLt6] at hk
        have hkSub : (⟨k.val + 1 - 1, by omega⟩ : Fin 5) = k :=
          Fin.ext (Nat.add_sub_cancel k.val 1)
        simpa only [hkSub] using hk
      have hdLimbs : pack256ToLimbs56 dom1 = pack256ToLimbs56 dom2 := by
        funext k
        have hk := congrArg (fun f => f ⟨k.val + 6, by omega⟩) hFunEq
        dsimp only [migrationNullifierInput] at hk
        have hNe0 : k.val + 6 ≠ 0 := by omega
        have hNotLt6 : ¬ (k.val + 6 < 6) := by omega
        rw [cIte_neg hNe0, cIte_neg hNe0] at hk
        simp only [hNotLt6, ↓reduceDIte] at hk
        have hkSub : (⟨k.val + 6 - 6, by omega⟩ : Fin 5) = k :=
          Fin.ext (Nat.add_sub_cancel k.val 6)
        simpa only [hkSub] using hk
      exact ⟨hgEq, pack256ToLimbs56_injective hsLimbs, pack256ToLimbs56_injective hdLimbs⟩
  cases hInEqDec with
  | isTrue hSameIn =>
    left
    have hgEq : g1 = g2 := by
      have hTag := congrArg (fun f => (f ⟨0, by decide⟩).val) hSameIn
      dsimp only [migrationNullifierInput] at hTag
      cases g1 <;> cases g2 <;> simp [ScalarGroup.nullifierTag] at hTag ⊢
    have hsLimbs : pack256ToLimbs56 s1 = pack256ToLimbs56 s2 := by
      funext k
      have hk := congrArg (fun f => f ⟨k.val + 1, by omega⟩) hSameIn
      dsimp only [migrationNullifierInput] at hk
      have hNe0 : k.val + 1 ≠ 0 := by omega
      have hLt6 : k.val + 1 < 6 := by omega
      rw [cIte_neg hNe0, cDIte_pos hLt6, cIte_neg hNe0, cDIte_pos hLt6] at hk
      have hkSub : (⟨k.val + 1 - 1, by omega⟩ : Fin 5) = k :=
        Fin.ext (Nat.add_sub_cancel k.val 1)
      simpa only [hkSub] using hk
    have hdLimbs : pack256ToLimbs56 dom1 = pack256ToLimbs56 dom2 := by
      funext k
      have hk := congrArg (fun f => f ⟨k.val + 6, by omega⟩) hSameIn
      dsimp only [migrationNullifierInput] at hk
      have hNe0 : k.val + 6 ≠ 0 := by omega
      have hNotLt6 : ¬ (k.val + 6 < 6) := by omega
      rw [cIte_neg hNe0, cIte_neg hNe0] at hk
      simp only [hNotLt6, ↓reduceDIte] at hk
      have hkSub : (⟨k.val + 6 - 6, by omega⟩ : Fin 5) = k :=
        Fin.ext (Nat.add_sub_cancel k.val 6)
      simpa only [hkSub] using hk
    exact ⟨hgEq, pack256ToLimbs56_injective hsLimbs, pack256ToLimbs56_injective hdLimbs⟩
  | isFalse hDiffIn =>
    exact Or.inr ⟨hDiffIn, hNullEq⟩

/-- A constant hash destroys nullifier binding; the collision alternative is necessary. -/
theorem tooth_constant_hash_nullifier_collision :
    ∃ (hash : UInt64 → (Fin 11 → Goldilocks) → (Fin 4 → Goldilocks))
      (g : ScalarGroup) (s d d' : BitVec 256),
      d ≠ d' ∧ computeMigrationNullifier hash g s d = computeMigrationNullifier hash g s d' := by
  refine ⟨fun _ _ _ => Goldilocks.zero, .Secp256k1, 0, 0, 1, ?_, rfl⟩
  decide

set_option maxRecDepth 4096 in
#tooth_pair Qsag.post_ceremony_nullifier_domain_binding_and_replay_sound vs
  Qsag.tooth_constant_hash_nullifier_collision

/-! ## 3. 3-Party 64-Lane Replicated Secret Sharing (`RssBit64`) & `shareUniformLanesCheck` -/

/-- Local 2-of-3 replicated 64-lane bit share `Bit([s_i, s_{i+1}])` held by custodian `i : Fin 3`
    (`outer_mpc.rs:1683, 1706`). -/
structure RssBit64 where
  mine : UInt64
  next : UInt64
  deriving Repr, DecidableEq

/-- Complete 3-custodian 64-lane replicated sharing `(w0, w1, w2)` of `w0 ^^^ w1 ^^^ w2`. -/
structure RssWord64Shares3 where
  w0 : UInt64
  w1 : UInt64
  w2 : UInt64
  deriving Repr, DecidableEq

/-- Replicated share pair `(s_i, s_{(i+1)%3})` visible to custodian `i : Fin 3` (`outer_mpc.rs:1703-1707`). -/
def RssWord64Shares3.partyView (sh : RssWord64Shares3) (i : Fin 3) : RssBit64 :=
  if i.val == 0 then ⟨sh.w0, sh.w1⟩
  else if i.val == 1 then ⟨sh.w1, sh.w2⟩
  else ⟨sh.w2, sh.w0⟩

/-- Reconstructed 64-lane word `(w0 ^^^ w1) ^^^ w2`. -/
def RssWord64Shares3.reconstruct (sh : RssWord64Shares3) : UInt64 :=
  (sh.w0 ^^^ sh.w1) ^^^ sh.w2

/-- Replica-consistency check in `Engine::open_raw_bits` (`outer_mpc.rs:1860-1869`). -/
def openRawBitsConsistent (p0 p1 p2 : RssBit64) : Bool :=
  (p0.next == p1.mine) && (p1.next == p2.mine) && (p2.next == p0.mine)

theorem openRawBitsConsistent_honest (sh : RssWord64Shares3) :
    openRawBitsConsistent
      (sh.partyView ⟨0, by decide⟩)
      (sh.partyView ⟨1, by decide⟩)
      (sh.partyView ⟨2, by decide⟩) = true := by
  have hRefl : ∀ x : UInt64, (x == x) = true := fun x => decide_eq_true (rfl : x = x)
  change ((sh.w1 == sh.w1) && (sh.w2 == sh.w2) && (sh.w0 == sh.w0)) = true
  rw [hRefl sh.w1, hRefl sh.w2, hRefl sh.w0]
  rfl

/-- 3-of-3 custodian shares of the normalized 256-bit spending scalar (`co_zk_mpc.rs:29-39`). -/
structure RssKeyShares3 where
  s0 : MigrationKey256
  s1 : MigrationKey256
  s2 : MigrationKey256
  deriving Repr, DecidableEq

/-- True underlying 256-bit spending scalar `s = (s0 ^^^ s1) ^^^ s2`. -/
@[expose] def RssKeyShares3.secret (ks : RssKeyShares3) : MigrationKey256 :=
  (ks.s0 ^^^ ks.s1) ^^^ ks.s2

/-- Broadcast a single witness share bit across all 64 ZKBoo batch lanes (`co_zk_mpc.rs:129`). -/
def expandUniformLane64 (b : Bool) : UInt64 :=
  if b then 0xFFFFFFFFFFFFFFFF else 0

/-- Check that a 64-lane witness word is uniform (`0` or `u64::MAX`, `outer_mpc.rs:1693, 1697`). -/
def isUniformLaneWord (w : UInt64) : Bool :=
  (w == 0) || (w == 0xFFFFFFFFFFFFFFFF)

/-- Constructive bounded universal quantifier over `Fin n`. -/
def finAll : (n : Nat) → (Fin n → Bool) → Bool
  | 0, _ => true
  | n + 1, p => p ⟨0, Nat.zero_lt_succ n⟩ && finAll n (fun i => p ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)

theorem finAll_eq_true_iff : ∀ (n : Nat) (p : Fin n → Bool),
    finAll n p = true ↔ ∀ i : Fin n, p i = true
  | 0, _ => ⟨fun _ i => Fin.elim0 i, fun _ => rfl⟩
  | n + 1, p => by
    simp only [finAll, Bool.and_eq_true, finAll_eq_true_iff n]
    constructor
    · rintro ⟨h0, hRest⟩ ⟨k, hk⟩
      cases k with
      | zero => exact h0
      | succ j => exact hRest ⟨j, Nat.lt_of_succ_lt_succ hk⟩
    · intro hAll
      exact ⟨hAll ⟨0, Nat.zero_lt_succ n⟩, fun i => hAll ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩⟩

/-- 256-bit × 64-lane replicated witness sharing across the 3 custodians (`co_zk_mpc.rs:126-131`). -/
structure RssWitnessLanes3 where
  w0 : Fin 256 → UInt64
  w1 : Fin 256 → UInt64
  w2 : Fin 256 → UInt64

/-- Build 64-lane witness words when custodian `0` injects per-bit 64-lane fault `deltaLanes`. -/
def buildWitnessLanes3 (ks : RssKeyShares3) (deltaLanes : Fin 256 → UInt64) : RssWitnessLanes3 where
  w0 j := expandUniformLane64 (ks.s0.getLsbD j.val) ^^^ deltaLanes j
  w1 j := expandUniformLane64 (ks.s1.getLsbD j.val)
  w2 j := expandUniformLane64 (ks.s2.getLsbD j.val)

/-- `Engine::share_uniform_lanes` check enforcing `0` or `u64::MAX` on every custodian's 256 words
    before batch splitting (`outer_mpc.rs:1692-1711`, `co_zk_mpc.rs:131`). -/
@[expose] def shareUniformLanesCheck (wl : RssWitnessLanes3) : Bool :=
  finAll 256 (fun j =>
    isUniformLaneWord (wl.w0 j) && isUniformLaneWord (wl.w1 j) && isUniformLaneWord (wl.w2 j))

/-- Extract the reconstructed 256-bit candidate witness evaluated by ZKBoo repetition `lane < 64`. -/
def extractRepetitionWitness (wl : RssWitnessLanes3) (lane : Nat) : MigrationKey256 :=
  packBits 256 (fun j =>
    if hj : j < 256 then
      let recon := (wl.w0 ⟨j, hj⟩ ^^^ wl.w1 ⟨j, hj⟩) ^^^ wl.w2 ⟨j, hj⟩
      recon.toBitVec.getLsbD lane
    else
      false)

private theorem isUniformLaneWord_or {w : UInt64} (hw : isUniformLaneWord w = true) :
    w = 0 ∨ w = 0xFFFFFFFFFFFFFFFF := by
  unfold isUniformLaneWord at hw
  cases h0 : (w == 0)
  · rw [h0, Bool.false_or] at hw
    exact Or.inr (eq_of_beq hw)
  · exact Or.inl (eq_of_beq h0)

private theorem isUniformLaneWord_xor {a b : UInt64}
    (ha : isUniformLaneWord a = true) (hb : isUniformLaneWord b = true) :
    isUniformLaneWord (a ^^^ b) = true := by
  rcases isUniformLaneWord_or ha with rfl | rfl <;>
    rcases isUniformLaneWord_or hb with rfl | rfl <;>
    decide

private theorem uniformLaneWord_getLsbD_eq {w : UInt64}
    (hw : isUniformLaneWord w = true) {l1 l2 : Nat} (hl1 : l1 < 64) (hl2 : l2 < 64) :
    w.toBitVec.getLsbD l1 = w.toBitVec.getLsbD l2 := by
  have hAll1 : (0xFFFFFFFFFFFFFFFF : UInt64).toBitVec = BitVec.allOnes 64 := by decide
  rcases isUniformLaneWord_or hw with rfl | rfl
  · simp
  · rw [hAll1, Qsag.Constructive.getLsbD_allOnes, Qsag.Constructive.getLsbD_allOnes,
        decide_eq_true hl1, decide_eq_true hl2]

private theorem expandUniformLane64_getLsbD (b : Bool) {lane : Nat} (hLane : lane < 64) :
    (expandUniformLane64 b).toBitVec.getLsbD lane = b := by
  have hAll1 : (0xFFFFFFFFFFFFFFFF : UInt64).toBitVec = BitVec.allOnes 64 := by decide
  cases b
  · simp [expandUniformLane64]
  · simp only [expandUniformLane64, ↓reduceIte, hAll1, Qsag.Constructive.getLsbD_allOnes,
      decide_eq_true hLane]

/-- **64-Lane Witness Uniformity (`shareUniformLanesCheck_implies_uniform_witness_across_lanes`)**:
    1. Whenever `shareUniformLanesCheck wl = true`, all 64 ZKBoo batch lanes reconstruct the
       **identical** 256-bit candidate spending key (`extractRepetitionWitness wl l1 = extractRepetitionWitness wl l2`).
    2. Any uniform 256-bit scalar fault `delta : MigrationKey256` passes `shareUniformLanesCheck`
       and shifts **every** lane `lane < 64` identically to `ks.secret ^^^ delta`. -/
theorem shareUniformLanesCheck_implies_uniform_witness_across_lanes :
    (∀ (wl : RssWitnessLanes3),
      shareUniformLanesCheck wl = true →
      ∀ l1 l2 : Nat, l1 < 64 → l2 < 64 →
        extractRepetitionWitness wl l1 = extractRepetitionWitness wl l2) ∧
    (∀ (ks : RssKeyShares3) (delta : MigrationKey256),
      let wl := buildWitnessLanes3 ks (fun j => expandUniformLane64 (delta.getLsbD j.val))
      shareUniformLanesCheck wl = true ∧
      ∀ lane : Nat, lane < 64 → extractRepetitionWitness wl lane = ks.secret ^^^ delta) := by
  refine ⟨?_, ?_⟩
  · intro wl hCheck l1 l2 hl1 hl2
    have hAll := (finAll_eq_true_iff 256 _).mp hCheck
    apply bv_eq_of_getLsbD_eq
    intro j hj
    unfold extractRepetitionWitness
    rw [packBits_getLsbD _ _ j hj, packBits_getLsbD _ _ j hj, cDIte_pos hj, cDIte_pos hj]
    have hjCheck := hAll ⟨j, hj⟩
    rw [Bool.and_eq_true, Bool.and_eq_true] at hjCheck
    have hReconUnif : isUniformLaneWord ((wl.w0 ⟨j, hj⟩ ^^^ wl.w1 ⟨j, hj⟩) ^^^ wl.w2 ⟨j, hj⟩) = true :=
      isUniformLaneWord_xor (isUniformLaneWord_xor hjCheck.1.1 hjCheck.1.2) hjCheck.2
    exact uniformLaneWord_getLsbD_eq hReconUnif hl1 hl2
  · intro ks delta wl
    have hUnifBool : ∀ b : Bool, isUniformLaneWord (expandUniformLane64 b) = true := by
      intro b; cases b <;> decide
    have hWlCheck : shareUniformLanesCheck wl = true := by
      rw [shareUniformLanesCheck, finAll_eq_true_iff]
      intro j
      dsimp only [wl, buildWitnessLanes3]
      rw [Bool.and_eq_true, Bool.and_eq_true]
      exact ⟨⟨isUniformLaneWord_xor (hUnifBool _) (hUnifBool _), hUnifBool _⟩, hUnifBool _⟩
    refine ⟨hWlCheck, ?_⟩
    intro lane hLane
    apply bv_eq_of_getLsbD_eq
    intro j hj
    unfold extractRepetitionWitness
    rw [packBits_getLsbD _ _ j hj, cDIte_pos hj]
    dsimp only [wl, buildWitnessLanes3]
    simp only [u64_toBitVec_xor, BitVec.getLsbD_xor, expandUniformLane64_getLsbD _ hLane,
      RssKeyShares3.secret]
    bv_xor_cancel

/-- **`#tooth` Skipping `share_uniform_lanes` Splits Witness Across Repetitions (`tooth_non_uniform_lanes_split_witness_across_reps`)**:
    If `share` is called instead of `share_uniform_lanes`, custodian `0` can inject a mixed 64-lane
    mask (`1 : UInt64` on bit `0`, flipping lane `0` only while leaving lane `1` untouched):
    `shareUniformLanesCheck` catches it (`= false`), whereas without the check lane `0` evaluates
    `ks.secret ^^^ oneBitMask 256 0` while lane `1` evaluates `ks.secret` (`≠`)! -/
theorem tooth_non_uniform_lanes_split_witness_across_reps_witness (ks : RssKeyShares3) :
    ∃ wl : RssWitnessLanes3,
      extractRepetitionWitness wl 0 ≠ extractRepetitionWitness wl 1 ∧
      shareUniformLanesCheck wl = false ∧
      extractRepetitionWitness wl 0 = ks.secret ^^^ oneBitMask 256 0 ∧
      extractRepetitionWitness wl 1 = ks.secret := by
  let mixedFault : Fin 256 → UInt64 := fun j => if j.val == 0 then 1 else 0
  let wl := buildWitnessLanes3 ks mixedFault
  have hCheckFalse : shareUniformLanesCheck wl = false := by
    cases h : shareUniformLanesCheck wl
    · rfl
    · exfalso
      have h0 := (finAll_eq_true_iff 256 _).mp h ⟨0, by decide⟩
      rw [Bool.and_eq_true, Bool.and_eq_true] at h0
      have hw0 : isUniformLaneWord (wl.w0 ⟨0, by decide⟩) = true := h0.1.1
      dsimp only [wl, buildWitnessLanes3, mixedFault] at hw0
      rcases isUniformLaneWord_or hw0 with hA | hB
      · cases hb : ks.s0.getLsbD 0 <;> rw [hb] at hA <;> revert hA <;> decide
      · cases hb : ks.s0.getLsbD 0 <;> rw [hb] at hB <;> revert hB <;> decide
  have hLane0 : extractRepetitionWitness wl 0 = ks.secret ^^^ oneBitMask 256 0 := by
    apply bv_eq_of_getLsbD_eq
    intro j hj
    unfold extractRepetitionWitness
    rw [packBits_getLsbD _ _ j hj, cDIte_pos hj, BitVec.getLsbD_xor, oneBitMask_getLsbD 256 0 j hj]
    dsimp only [wl, buildWitnessLanes3, mixedFault]
    simp only [u64_toBitVec_xor, BitVec.getLsbD_xor, expandUniformLane64_getLsbD _ (by decide : 0 < 64),
      RssKeyShares3.secret]
    cases hjeq : (j == 0)
    · have hjNe : j ≠ 0 := fun h => by subst h; cases hjeq
      rw [decide_eq_false hjNe]
      simp only [Bool.false_eq_true, ↓reduceIte]
      have h0Bit : ((0 : UInt64).toBitVec).getLsbD 0 = false := by decide
      rw [h0Bit]
      bv_xor_cancel
    · have hjEq0 : j = 0 := eq_of_beq hjeq
      subst hjEq0
      simp only [↓reduceIte, decide_true]
      have h1Bit : ((1 : UInt64).toBitVec).getLsbD 0 = true := by decide
      rw [h1Bit]
      cases ks.s0.getLsbD 0 <;> cases ks.s1.getLsbD 0 <;> cases ks.s2.getLsbD 0 <;> rfl
  have hLane1 : extractRepetitionWitness wl 1 = ks.secret := by
    apply bv_eq_of_getLsbD_eq
    intro j hj
    unfold extractRepetitionWitness
    rw [packBits_getLsbD _ _ j hj, cDIte_pos hj]
    dsimp only [wl, buildWitnessLanes3, mixedFault]
    simp only [u64_toBitVec_xor, BitVec.getLsbD_xor, expandUniformLane64_getLsbD _ (by decide : 1 < 64),
      RssKeyShares3.secret]
    cases (j == 0)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have h0Bit : ((0 : UInt64).toBitVec).getLsbD 1 = false := by decide
      rw [h0Bit]
      bv_xor_cancel
    · simp only [↓reduceIte]
      have h1Bit : ((1 : UInt64).toBitVec).getLsbD 1 = false := by decide
      rw [h1Bit]
      bv_xor_cancel
  have hNe : extractRepetitionWitness wl 0 ≠ extractRepetitionWitness wl 1 := by
    rw [hLane0, hLane1]
    intro hEq
    have hBit0 := congrArg (·.getLsbD 0) hEq
    have hDec0 : decide (0 = (0 : Nat)) = true := rfl
    rw [BitVec.getLsbD_xor, oneBitMask_getLsbD 256 0 0 (by decide), hDec0] at hBit0
    cases hb : ks.secret.getLsbD 0 <;> rw [hb] at hBit0 <;> cases hBit0
  exact ⟨wl, hNe, hCheckFalse, hLane0, hLane1⟩

theorem tooth_non_uniform_lanes_split_witness_across_reps (ks : RssKeyShares3) :
    ¬ (∀ wl : RssWitnessLanes3,
        shareUniformLanesCheck wl = true ∨
        extractRepetitionWitness wl 0 = extractRepetitionWitness wl 1) := by
  intro hAll
  obtain ⟨wl, hNe, hCheckFalse, _, _⟩ := tooth_non_uniform_lanes_split_witness_across_reps_witness ks
  rcases hAll wl with hTrue | hEq
  · rw [hCheckFalse] at hTrue; cases hTrue
  · exact hNe hEq

#tooth_pair
  Qsag.shareUniformLanesCheck_implies_uniform_witness_across_lanes
  vs
  Qsag.tooth_non_uniform_lanes_split_witness_across_reps

/-! ## 4. Premature Residual Opening Key-Recovery `#tooth` on Canonical `Secp256k1` & `Ed25519` -/

/-- Honest verifier rejection codes matching `outer_mpc::Error` (`co_zk_mpc.rs:750, 1108`). -/
inductive CeremonyAbortError where
  | laneDisagreement
  | invalidTape
  | multiplicationCheck
  | invalidProof
  deriving Repr, DecidableEq

/-- Broken ceremony protocol (prior to inside-MPC `all_outputs_zero` gating): opens the raw curve
    residual `encodePk (pkOf s') ^^^ encodePk pk` publicly *before* checking `allOutputsZero`. -/
def brokenPrematureOpenCeremony {w pWidth : Nat} {PubKey ZkView : Type}
    (pkOf : BitVec w → PubKey) (encodePk : PubKey → BitVec pWidth)
    (zkCommit : BitVec w → ZkView) (pk : PubKey)
    (s0 s1 s2 delta : BitVec w) :
    BitVec pWidth × Except CeremonyAbortError ZkView :=
  let s' := ((s0 ^^^ delta) ^^^ s1) ^^^ s2
  let res := encodePk (pkOf s') ^^^ encodePk pk
  let verdict :=
    if res != 0#pWidth then .error .invalidProof
    else .ok (zkCommit s')
  (res, verdict)

/-- Explicit `1`-query bit-extraction step from a prematurely opened residual on fault `oneBitMask w i`. -/
def extractSecretBitFromBrokenOpen {w pWidth : Nat} {PubKey : Type} [DecidableEq PubKey]
    (G : ScalarPointHom w pWidth PubKey) (pk : PubKey)
    (i : Nat) (openedResidual : BitVec pWidth) : Bool :=
  let unmaskedPkBits := openedResidual ^^^ G.encodePk pk
  unmaskedPkBits != G.encodePk (G.ptAdd pk (G.genBit i))

/-- Explicit `w`-query spending-key recovery algorithm over prematurely opened ceremony residuals. -/
def recoverKeyFromPrematureOpens {w pWidth : Nat} {PubKey : Type} [DecidableEq PubKey]
    (G : ScalarPointHom w pWidth PubKey) (pk : PubKey)
    (queryResidualAtBit : Nat → BitVec pWidth) : BitVec w :=
  packBits w (fun i => extractSecretBitFromBrokenOpen G pk i (queryResidualAtBit i))

/-- **`#tooth` Premature Residual Opening Key-Recovery Attack (`tooth_premature_residual_open_recovers_spending_key`)**:
    On `brokenPrematureOpenCeremony` (opening `res` before verifying `all_outputs_zero`):
    1. Every single-bit fault ceremony `delta = oneBitMask w i` (`i < w`) is rejected by the honest
       custodians with `.error .invalidProof`, AND
    2. `recoverKeyFromPrematureOpens` deterministically recovers the **entire** `w`-bit secret
       spending key `(s0 ^^^ s1) ^^^ s2` with probability `1`! -/
theorem tooth_premature_residual_open_recovers_spending_key
    {w pWidth : Nat} {PubKey ZkView : Type} [DecidableEq PubKey]
    (G : ScalarPointHom w pWidth PubKey)
    (zkCommit : BitVec w → ZkView)
    (s0 s1 s2 : BitVec w) :
    ∃ recovered : BitVec w,
      recovered = recoverKeyFromPrematureOpens G (scalarMulKey G ((s0 ^^^ s1) ^^^ s2))
        (fun i => (brokenPrematureOpenCeremony (scalarMulKey G) G.encodePk zkCommit
          (scalarMulKey G ((s0 ^^^ s1) ^^^ s2)) s0 s1 s2 (oneBitMask w i)).1) ∧
      recovered = (s0 ^^^ s1) ^^^ s2 ∧
      (∀ i, i < w →
        (brokenPrematureOpenCeremony (scalarMulKey G) G.encodePk zkCommit
          (scalarMulKey G ((s0 ^^^ s1) ^^^ s2)) s0 s1 s2 (oneBitMask w i)).2 = .error .invalidProof) := by
  let secret := (s0 ^^^ s1) ^^^ s2
  let pk := scalarMulKey G secret
  let runBitQuery := fun i =>
    brokenPrematureOpenCeremony (scalarMulKey G) G.encodePk zkCommit pk s0 s1 s2 (oneBitMask w i)
  have hEncInj := G.encodePk_injective
  have hShift : ∀ d : BitVec w, ((s0 ^^^ d) ^^^ s1) ^^^ s2 = secret ^^^ d := by
    intro d; dsimp only [secret]; bv_xor_cancel
  have hBitExact : ∀ i, i < w →
      extractSecretBitFromBrokenOpen G pk i (runBitQuery i).1 = secret.getLsbD i ∧
      (runBitQuery i).2 = .error .invalidProof := by
    intro i hi
    simp only [runBitQuery, brokenPrematureOpenCeremony, extractSecretBitFromBrokenOpen, hShift]
    have hUnmask : (G.encodePk (scalarMulKey G (secret ^^^ oneBitMask w i)) ^^^ G.encodePk pk) ^^^
        G.encodePk pk = G.encodePk (scalarMulKey G (secret ^^^ oneBitMask w i)) := by
      bv_xor_cancel
    rw [hUnmask, scalarMulKey_xor_oneBit G secret hi]
    dsimp only [pk]
    have hNon2 : G.ptAdd pk (G.genBit i) ≠ G.ptSub pk (G.genBit i) := G.non_two_torsion i hi pk
    have hGenNeZero : G.ptAdd pk (G.genBit i) ≠ pk ∧ G.ptSub pk (G.genBit i) ≠ pk := by
      constructor
      · intro hAddEq
        have hSubEq : G.ptSub pk (G.genBit i) = pk := by
          have h1 := congrArg (fun u => G.ptSub u (G.genBit i)) hAddEq
          rw [G.add_sub_cancel] at h1
          exact h1.symm
        exact hNon2 (hAddEq.trans hSubEq.symm)
      · intro hSubEq
        have hAddEq : G.ptAdd pk (G.genBit i) = pk := by
          have h1 := congrArg (fun u => G.ptAdd u (G.genBit i)) hSubEq
          rw [G.sub_add_cancel] at h1
          exact h1.symm
        exact hNon2 (hAddEq.trans hSubEq.symm)
    cases hBit : secret.getLsbD i
    · simp only [Bool.false_eq_true, ↓reduceIte, bne_self_eq_false]
      have hResTrue : (G.encodePk (G.ptAdd pk (G.genBit i)) ^^^ G.encodePk pk != 0#pWidth) = true := by
        rw [bv_bne_zero_eq_true_iff_ne]
        exact fun hEq => hGenNeZero.1 (hEncInj hEq)
      rw [hResTrue]
      exact ⟨trivial, rfl⟩
    · simp only [↓reduceIte]
      have hNeEnc : G.encodePk (G.ptSub pk (G.genBit i)) ≠ G.encodePk (G.ptAdd pk (G.genBit i)) :=
        fun hEq => hNon2 (hEncInj hEq).symm
      have hResTrue : (G.encodePk (G.ptSub pk (G.genBit i)) ^^^ G.encodePk pk != 0#pWidth) = true := by
        rw [bv_bne_zero_eq_true_iff_ne]
        exact fun hEq => hGenNeZero.2 (hEncInj hEq)
      rw [bne_iff_ne.mpr hNeEnc, hResTrue]
      exact ⟨rfl, rfl⟩
  have hRec : recoverKeyFromPrematureOpens G pk (fun i => (runBitQuery i).1) = secret := by
    apply bv_eq_of_getLsbD_eq
    intro i hi
    unfold recoverKeyFromPrematureOpens
    rw [packBits_getLsbD _ _ i hi]
    exact (hBitExact i hi).1
  exact ⟨secret, hRec.symm, rfl, fun i hi => (hBitExact i hi).2⟩

/-- Concrete instantiation of `tooth_premature_residual_open_recovers_spending_key` over canonical
    `< group.orderNat` scalars for **both** `ScalarGroup.Secp256k1` (`SECP_N`) and
    `ScalarGroup.Ed25519` (`ED_ORDER`) (`0` `Fin (2^w + 1)` scaffolding!). -/
theorem tooth_premature_residual_open_recovers_canonical_spending_key
    {ZkView : Type} (group : ScalarGroup) (zkCommit : MigrationKey256 → ZkView)
    (ks : RssKeyShares3) (hCanon : requireCanonicalScalar group ks.secret = true) :
    let G := canonicalSubgroupHom group
    let pk := scalarMulKey G ks.secret
    let runBitQuery := fun i =>
      brokenPrematureOpenCeremony (scalarMulKey G) G.encodePk zkCommit pk ks.s0 ks.s1 ks.s2 (oneBitMask 256 i)
    0 < ks.secret.toNat ∧
    ks.secret.toNat < group.orderNat ∧
    recoverKeyFromPrematureOpens G pk (fun i => (runBitQuery i).1) = ks.secret ∧
    (∀ i, i < 256 → (runBitQuery i).2 = .error .invalidProof) := by
  obtain ⟨hPos, hLt⟩ := (requireCanonicalScalar_iff group ks.secret).mp hCanon
  obtain ⟨_, hRecEq, hSecEq, hErr⟩ := tooth_premature_residual_open_recovers_spending_key
    (canonicalSubgroupHom group) zkCommit ks.s0 ks.s1 ks.s2
  exact ⟨hPos, hLt, hRecEq.symm.trans hSecEq, hErr⟩

/-! ## 5. Algebraic `GF(2^128)` (`Tower128`) BBCGGI19 Sacrifice & Coin-Permuted Triple Bucketing -/

/-- Multiplication triple `(x, y, z)` over `Tower128` (`GF(2^128)`, `outer_mpc.rs:1906-2384`). -/
structure Gf2128MulTriple where
  x : Tower128
  y : Tower128
  z : Tower128
  deriving DecidableEq

/-- Additive multiplication error `delta = z - x * y = z + x * y` in characteristic-2 `Tower128`. -/
def tripleMulError (t : Gf2128MulTriple) : Tower128 :=
  towerAdd 7 t.z (towerMul 7 t.x t.y)

theorem tripleMulError_eq_zero_iff (t : Gf2128MulTriple) :
    tripleMulError t = towerZero 7 ↔ t.z = towerMul 7 t.x t.y := by
  unfold tripleMulError
  constructor
  · intro h
    have hAdd := congrArg (fun u => towerAdd 7 u (towerMul 7 t.x t.y)) h
    rw [towerAdd_assoc, towerAdd_self_zero, towerAdd_zero, towerZero_add] at hAdd
    exact hAdd
  · intro h
    rw [h, towerAdd_self_zero]

/-- Algebraic `GF(2^128)` BBCGGI19 polynomial sacrifice check (`outer_mpc.rs:1932-2384, 2991-3000`):
    given random base-case mask triple `maskTriple` (`delta_0 = tripleMulError maskTriple`) and
    `m` pending multiplication triples `triples` (`delta_k = tripleMulError t_k`), checks
    `delta_0 + ∑_{k=1}^m chi^k · delta_k = 0` over `Tower128`! -/
@[expose] def verifyAllPendingGf2128
    (maskTriple : Gf2128MulTriple) (triples : List Gf2128MulTriple) (chi : Tower128) : Bool :=
  decide (RoundPoly.evalCoeffs (tripleMulError maskTriple :: triples.map tripleMulError) chi = towerZero 7)

private theorem evalCoeffs_all_zero : ∀ (n : Nat) (chi : Tower128),
    RoundPoly.evalCoeffs (List.replicate n (towerZero 7)) chi = towerZero 7
  | 0, _ => rfl
  | n + 1, chi => by
    simp only [List.replicate, RoundPoly.evalCoeffs_cons, evalCoeffs_all_zero n chi]
    change towerAdd 7 (towerZero 7) (towerMul 7 chi (towerZero 7)) = towerZero 7
    rw [towerMul_zero, towerAdd_zero]

theorem verifyAllPendingGf2128_honest_complete
    (maskTriple : Gf2128MulTriple) (triples : List Gf2128MulTriple)
    (hMask : maskTriple.z = towerMul 7 maskTriple.x maskTriple.y)
    (hTriples : ∀ t ∈ triples, t.z = towerMul 7 t.x t.y)
    (chi : Tower128) :
    verifyAllPendingGf2128 maskTriple triples chi = true := by
  unfold verifyAllPendingGf2128
  rw [decide_eq_true_eq]
  have h0 : tripleMulError maskTriple = towerZero 7 := (tripleMulError_eq_zero_iff maskTriple).mpr hMask
  have hMap : triples.map tripleMulError = List.replicate triples.length (towerZero 7) := by
    induction triples with
    | nil => rfl
    | cons hd tl ih =>
      simp only [List.map_cons, List.length_cons, List.replicate]
      rw [(tripleMulError_eq_zero_iff hd).mpr (hTriples hd (.head _)),
          ih (fun u hu => hTriples u (.tail _ hu))]
  rw [h0, hMap]
  exact evalCoeffs_all_zero (triples.length + 1) chi

/-- Embed `< 2^128` naturals into distinct `Tower128` elements via `unpackTower 7`. -/
def tower128OfNat (n : Nat) : Tower128 :=
  unpackTower 7 (BitVec.ofNat 128 n)

private theorem tower128OfNat_injective_lt {a b : Nat}
    (ha : a < 2 ^ 128) (hb : b < 2 ^ 128)
    (hEq : tower128OfNat a = tower128OfNat b) : a = b := by
  have hp := congrArg (packTower 7) hEq
  unfold tower128OfNat at hp
  rw [packTower_unpackTower, packTower_unpackTower] at hp
  have hn := congrArg BitVec.toNat hp
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hn
  exact hn

private theorem tower128OfNat_ne_zero {a : Nat} (hPos : 0 < a) (ha : a < 2 ^ 128) :
    tower128OfNat a ≠ towerZero 7 := by
  intro hZero
  have h0 : towerZero 7 = tower128OfNat 0 := by
    unfold tower128OfNat
    have hb0 : BitVec.ofNat 128 0 = (0 : TowerBitVec 7) := rfl
    rw [hb0, unpackTower_zero]
  rw [h0] at hZero
  have ha0 := tower128OfNat_injective_lt ha (Nat.two_pow_pos 128) hZero
  omega

private theorem nodup_map_on_list {α β : Type} (f : α → β) :
    ∀ {l : List α}, l.Nodup → (∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) → (l.map f).Nodup
  | [], _, _ => .nil
  | a :: tl, .cons hNotMem hNdTl, hInj => by
    simp only [List.map_cons]
    refine .cons ?_ (nodup_map_on_list f hNdTl (fun x hx y hy hEq => hInj x (.tail _ hx) y (.tail _ hy) hEq))
    intro b hbMem hEq
    rcases List.mem_map.mp hbMem with ⟨a', ha'Mem, rfl⟩
    have haEq : a = a' := hInj a (.head _) a' (.tail _ ha'Mem) hEq
    subst haEq
    exact hNotMem a ha'Mem rfl

private theorem exists_mem_of_filter_length_lt {α : Type} (p : α → Bool) :
    ∀ (l : List α), (l.filter p).length < l.length → ∃ x ∈ l, p x = false
  | [], h => False.elim (Nat.lt_irrefl 0 h)
  | a :: tl, h => by
    simp only [List.filter] at h
    cases hp : p a
    · exact ⟨a, .head _, hp⟩
    · rw [hp] at h
      simp only [List.length_cons] at h
      obtain ⟨x, hxMem, hxFalse⟩ := exists_mem_of_filter_length_lt p tl (Nat.lt_of_succ_lt_succ h)
      exact ⟨x, .tail _ hxMem, hxFalse⟩

/-- Constructive (`0` choice axioms) polynomial non-triviality over `Tower128`:
    any coefficient list `cs : List Tower128` of length `< 2^128` with at least one nonzero
    coefficient evaluates to a nonzero `Tower128` value at an explicit point `x₀`. -/
theorem exists_eval_nonzero_tower128 :
    ∀ (cs : List Tower128),
      cs.length < 2 ^ 128 →
      (∃ c ∈ cs, c ≠ towerZero 7) →
      ∃ x₀ : Tower128, RoundPoly.evalCoeffs cs x₀ ≠ towerZero 7
  | [], _, ⟨_, hMem, _⟩ => by cases hMem
  | c₀ :: tail, hLen, ⟨c, hMem, hcNe⟩ => by
    cases towerDecidableEq 7 c₀ (towerZero 7) with
    | isFalse hc0Ne =>
      refine ⟨towerZero 7, ?_⟩
      simp only [RoundPoly.evalCoeffs_cons]
      change towerAdd 7 c₀ (towerMul 7 (towerZero 7) (RoundPoly.evalCoeffs tail (towerZero 7))) ≠ towerZero 7
      rw [towerZero_mul, towerAdd_zero]
      exact hc0Ne
    | isTrue hc0Eq =>
      subst hc0Eq
      have hTailEx : ∃ c' ∈ tail, c' ≠ towerZero 7 := by
        rcases List.mem_cons.mp hMem with rfl | hInTail
        · exact False.elim (hcNe rfl)
        · exact ⟨c, hInTail, hcNe⟩
      have hTailPos : 1 ≤ tail.length := by
        rcases hTailEx with ⟨_, hm, _⟩
        cases tail with
        | nil => cases hm
        | cons _ _ => simp only [List.length_cons]; omega
      simp only [List.length_cons] at hLen
      have hTailLt : tail.length < 2 ^ 128 := by omega
      obtain ⟨x₁, hx₁⟩ := exists_eval_nonzero_tower128 tail hTailLt hTailEx
      let d := tail.length - 1
      let grid : List Tower128 := (List.range (d + 1)).map (fun i => tower128OfNat (i + 1))
      have hGridLen : grid.length = d + 1 := by simp [grid]
      have hGridNodup : grid.Nodup := by
        apply nodup_map_on_list _ (Qsag.Constructive.nodup_range (d + 1))
        intro a ha b hb hEq
        have haLt : a + 1 < 2 ^ 128 := by have := List.mem_range.mp ha; omega
        have hbLt : b + 1 < 2 ^ 128 := by have := List.mem_range.mp hb; omega
        have hSucc := tower128OfNat_injective_lt haLt hbLt hEq
        omega
      have hdLen : tail.length ≤ d + 1 := by omega
      have hRootsLe :
          (grid.filter (fun r => decide (RoundPoly.evalCoeffs tail r = towerZero 7))).length ≤ d :=
        RoundPoly.roots_nodup_length_le d tail grid hGridNodup hdLen ⟨x₁, hx₁⟩
      have hFiltLt :
          (grid.filter (fun r => decide (RoundPoly.evalCoeffs tail r = towerZero 7))).length < grid.length := by
        rw [hGridLen]; omega
      obtain ⟨x₀, hx₀Mem, hx₀False⟩ := exists_mem_of_filter_length_lt
        (fun r => decide (RoundPoly.evalCoeffs tail r = towerZero 7)) grid hFiltLt
      have hx₀NeZero : x₀ ≠ towerZero 7 := by
        rcases List.mem_map.mp hx₀Mem with ⟨idx, hIdxRange, rfl⟩
        have hIdxLt : idx < d + 1 := List.mem_range.mp hIdxRange
        exact tower128OfNat_ne_zero (by omega) (by omega)
      have hEvalTailNe : RoundPoly.evalCoeffs tail x₀ ≠ towerZero 7 := by
        intro hZero
        rw [decide_eq_true hZero] at hx₀False
        cases hx₀False
      refine ⟨x₀, ?_⟩
      simp only [RoundPoly.evalCoeffs_cons]
      change towerAdd 7 (towerZero 7) (towerMul 7 x₀ (RoundPoly.evalCoeffs tail x₀)) ≠ towerZero 7
      rw [towerZero_add]
      intro hProdZero
      rcases (towerMul_eq_zero_iff 7 x₀ (RoundPoly.evalCoeffs tail x₀)).mp hProdZero with h1 | h2
      · exact hx₀NeZero h1
      · exact hEvalTailNe h2

/-- **Algebraic `GF(2^128)` BBCGGI19 Multiplication-Sacrifice Soundness (`bbcggi19_gf2128_soundness_bound`)**:
    For any batch of `≤ m` multiplication triples (`m + 1 < 2^128`) and any base mask triple
    `maskTriple` (`delta_0`), if **at least one** multiplication gate carries a nonzero additive
    fault (`∃ t ∈ triples, tripleMulError t ≠ towerZero 7`), then across **any** duplicate-free
    challenge list `S : List Tower128` (`S.Nodup`), `verifyAllPendingGf2128` passes on **at most
    `m` challenges** (`≤ m / 2^128` over `GF(2^128)`), proved via `RoundPoly.roots_nodup_length_le`
    and `towerNoZeroDivisors 7`! -/
theorem bbcggi19_gf2128_soundness_bound
    (m : Nat) (hmBound : m + 1 < 2 ^ 128)
    (maskTriple : Gf2128MulTriple) (triples : List Gf2128MulTriple)
    (hBatchLen : triples.length ≤ m)
    (hFault : ∃ t ∈ triples, tripleMulError t ≠ towerZero 7)
    (S : List Tower128) (hNodup : S.Nodup) :
    let passing := S.filter (fun chi => verifyAllPendingGf2128 maskTriple triples chi)
    passing.length ≤ m ∧
    ratLe (passing.length, 2 ^ 128) (m, 2 ^ 128) := by
  intro passing
  let cs : List Tower128 := tripleMulError maskTriple :: triples.map tripleMulError
  have hCsLen : cs.length ≤ m + 1 := by
    simp only [cs, List.length_cons, List.length_map]
    omega
  have hCsLt128 : cs.length < 2 ^ 128 := by omega
  have hCoeffNz : ∃ c ∈ cs, c ≠ towerZero 7 := by
    obtain ⟨t, htMem, htNe⟩ := hFault
    exact ⟨tripleMulError t, .tail _ (List.mem_map_of_mem htMem), htNe⟩
  obtain ⟨x₀, hx₀⟩ := exists_eval_nonzero_tower128 cs hCsLt128 hCoeffNz
  have hRootsLe :
      (S.filter (fun chi => decide (RoundPoly.evalCoeffs cs chi = towerZero 7))).length ≤ m :=
    RoundPoly.roots_nodup_length_le m cs S hNodup hCsLen ⟨x₀, hx₀⟩
  have hPassLe : passing.length ≤ m := hRootsLe
  have hDenPos : 0 < 2 ^ 128 := Nat.two_pow_pos 128
  exact ⟨hPassLe, ⟨hDenPos, hDenPos, Nat.mul_le_mul_right (2 ^ 128) hPassLe⟩⟩

/-- **`#tooth` Unverified `AND` Gate Forges `all_outputs_zero = true` (`tooth_unverified_mul_forges_all_outputs_zero`)**:
    If `verify_all_pending()` is skipped before opening `all_outputs_zero`, a corrupt custodian `0`
    who flips their output share of the final `fold_all_true_bits` `AND` gate (`z := towerOne 7` on
    true inputs `(0, 0)`) forces `all_outputs_zero` to reconstruct to `true` on an invalid witness,
    whereas `verifyAllPendingGf2128` rejects the forged triple on every nonzero challenge `chi ≠ 0`! -/
theorem tooth_unverified_mul_forges_all_outputs_zero :
    ∃ honestZeroMask forgedFinalAnd : Gf2128MulTriple,
      forgedFinalAnd.z ≠ towerMul 7 forgedFinalAnd.x forgedFinalAnd.y ∧
      tripleMulError forgedFinalAnd ≠ towerZero 7 ∧
      (∀ chi : Tower128, chi ≠ towerZero 7 →
        verifyAllPendingGf2128 honestZeroMask [forgedFinalAnd] chi = false) := by
  let honestZeroMask : Gf2128MulTriple := ⟨towerZero 7, towerZero 7, towerZero 7⟩
  let forgedFinalAnd : Gf2128MulTriple := ⟨towerZero 7, towerZero 7, towerOne 7⟩
  have hErrEq : tripleMulError forgedFinalAnd = towerOne 7 := by
    unfold tripleMulError
    dsimp only [forgedFinalAnd]
    rw [towerMul_zero, towerAdd_zero]
  have hOneNe0 : towerOne 7 ≠ towerZero 7 := towerOne_ne_zero 7
  refine ⟨honestZeroMask, forgedFinalAnd, ?_, ?_, ?_⟩
  · dsimp only [forgedFinalAnd]
    rw [towerMul_zero]
    exact hOneNe0
  · rw [hErrEq]
    exact hOneNe0
  · intro chi hChiNe
    unfold verifyAllPendingGf2128
    have hMask0 : tripleMulError honestZeroMask = towerZero 7 := by
      unfold tripleMulError; dsimp only [honestZeroMask]; rw [towerMul_zero, towerAdd_zero]
    simp only [List.map_cons, List.map_nil, hMask0, hErrEq,
      RoundPoly.evalCoeffs_cons, RoundPoly.evalCoeffs_nil]
    change decide (towerAdd 7 (towerZero 7)
      (towerMul 7 chi (towerAdd 7 (towerOne 7) (towerMul 7 chi (towerZero 7)))) = towerZero 7) = false
    rw [towerMul_zero, towerAdd_zero, towerMul_one, towerZero_add]
    exact decide_eq_false hChiNe

#tooth_pair
  Qsag.bbcggi19_gf2128_soundness_bound
  vs
  Qsag.tooth_unverified_mul_forges_all_outputs_zero

/-- Authentic `Tower128` correlated-OT sender message `m_1 := (u_0 + a) + deltaM1`. -/
def otSenderMsg1Gf2128 (u0 a deltaM1 : Tower128) : Tower128 :=
  towerAdd 7 (towerAdd 7 u0 a) deltaM1

/-- Receiver's `Tower128` OT output `v := if b then m_1 else u_0` for choice bit `b : Bool`. -/
def otReceiverOutGf2128 (b : Bool) (u0 m1 : Tower128) : Tower128 :=
  if b then m1 else u0

/-- Algebraic `Tower128` correlation residual `(u_0 + v) + b · a`. -/
def otCorrelationResidualGf2128 (u0 a deltaM1 : Tower128) (b : Bool) : Tower128 :=
  towerAdd 7
    (towerAdd 7 u0 (otReceiverOutGf2128 b u0 (otSenderMsg1Gf2128 u0 a deltaM1)))
    (if b then a else towerZero 7)

/-- Algebraic `Tower128` MAC / sacrifice check `chi * residual == 0` over `GF(2^128)`. -/
def otSacrificeCheckGf2128 (chi u0 a deltaM1 : Tower128) (b : Bool) : Bool :=
  decide (towerMul 7 chi (otCorrelationResidualGf2128 u0 a deltaM1 b) = towerZero 7)

/-- Derived algebraic characterization of `otSacrificeCheckGf2128` via `towerNoZeroDivisors 7`:
    1. Honest OT correlation (`deltaM1 = 0`) passes for all `b`.
    2. Any nonzero `Tower128` fault `deltaM1 ≠ 0` under nonzero challenge `chi ≠ 0` passes **iff**
       the receiver's secret choice bit is `b = false` (`= !b`)! -/
theorem otSacrificeCheckGf2128_characterize (chi u0 a deltaM1 : Tower128) (b : Bool) :
    (deltaM1 = towerZero 7 → otSacrificeCheckGf2128 chi u0 a deltaM1 b = true) ∧
    (chi ≠ towerZero 7 → deltaM1 ≠ towerZero 7 →
      otSacrificeCheckGf2128 chi u0 a deltaM1 b = !b) := by
  have hRes : otCorrelationResidualGf2128 u0 a deltaM1 b = if b then deltaM1 else towerZero 7 := by
    unfold otCorrelationResidualGf2128 otReceiverOutGf2128 otSenderMsg1Gf2128
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte, towerAdd_self_zero]
    · simp only [↓reduceIte]
      rw [← towerAdd_assoc 7 u0 (towerAdd 7 u0 a) deltaM1,
          towerAdd_cancel 7 u0 a,
          towerAdd_comm 7 a deltaM1,
          towerAdd_assoc 7 deltaM1 a a,
          towerAdd_self_zero,
          towerAdd_zero]
  unfold otSacrificeCheckGf2128
  rw [hRes]
  refine ⟨?_, ?_⟩
  · intro hZero
    subst hZero
    cases b <;> simp [towerMul_zero]
  · intro hChi hDelta
    cases b
    · simp [towerMul_zero]
    · simp only [↓reduceIte, Bool.not_true]
      apply decide_eq_false
      intro hMul0
      rcases (towerMul_eq_zero_iff 7 chi deltaM1).mp hMul0 with h1 | h2
      · exact hChi h1
      · exact hDelta h2

/-- Uniform enumeration of `Bool` over `Fin 2`. -/
def boolSampleEnum : SimpleEquiv (Fin 2) Bool where
  toFun i := decide (i.val = 1)
  invFun b := if b then ⟨1, by omega⟩ else ⟨0, by omega⟩
  left_inv := fun ⟨v, hv⟩ => by
    match v with
    | 0 => rfl
    | 1 => rfl
    | _ + 2 => exact False.elim (by omega)
  right_inv b := by cases b <;> rfl

/-- Uniform enumeration of `Bool × Bool` (`4` equiprobable receiver bit pairs `(b_left, b_right)`). -/
def boolPairSampleEnum : SimpleEquiv (Fin 4) (Bool × Bool) where
  toFun i := (decide (i.val / 2 = 1), decide (i.val % 2 = 1))
  invFun p :=
    ⟨(if p.1 then 2 else 0) + (if p.2 then 1 else 0), by
      cases p.1 <;> cases p.2 <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega⟩
  left_inv := fun ⟨v, hv⟩ => by
    match v with
    | 0 =>
      have h : (⟨0, hv⟩ : Fin 4) = ⟨0, by decide⟩ := by apply Fin.ext; rfl
      rw [h]; decide
    | 1 =>
      have h : (⟨1, hv⟩ : Fin 4) = ⟨1, by decide⟩ := by apply Fin.ext; rfl
      rw [h]; decide
    | 2 =>
      have h : (⟨2, hv⟩ : Fin 4) = ⟨2, by decide⟩ := by apply Fin.ext; rfl
      rw [h]; decide
    | 3 =>
      have h : (⟨3, hv⟩ : Fin 4) = ⟨3, by decide⟩ := by apply Fin.ext; rfl
      rw [h]; decide
    | _ + 4 => exact False.elim (by omega)
  right_inv := fun ⟨b1, b2⟩ => by cases b1 <;> cases b2 <;> rfl

/-- Two-triple XOR bucket combine `b_final := b_left != b_right`. -/
def combineBucketBit (bLeft bRight : Bool) : Bool :=
  bLeft != bRight

/-- Online Beaver masked wire opening `e := y != b_final` for secret wire bit `y : Bool`. -/
def onlineBeaverOpenBit (y bFinal : Bool) : Bool :=
  y != bFinal

/-- Joint `Tower128` sacrifice survival event when an attacker injects nonzero `Tower128` OT faults
    `deltaL, deltaR` into both partner triples `(k, k + 2N)`. -/
def fixedBucketDoubleFaultSurvivesGf2128
    (chi u0L aL deltaL u0R aR deltaR : Tower128) (pair : Bool × Bool) : Bool :=
  otSacrificeCheckGf2128 chi u0L aL deltaL pair.1 &&
  otSacrificeCheckGf2128 chi u0R aR deltaR pair.2

private theorem fixedBucketDoubleFaultSurvivesGf2128_eq_both_false
    {chi u0L aL deltaL u0R aR deltaR : Tower128}
    (hChi : chi ≠ towerZero 7) (hDL : deltaL ≠ towerZero 7) (hDR : deltaR ≠ towerZero 7)
    (pair : Bool × Bool) :
    fixedBucketDoubleFaultSurvivesGf2128 chi u0L aL deltaL u0R aR deltaR pair =
      (!pair.1 && !pair.2) := by
  unfold fixedBucketDoubleFaultSurvivesGf2128
  rw [(otSacrificeCheckGf2128_characterize chi u0L aL deltaL pair.1).2 hChi hDL,
      (otSacrificeCheckGf2128_characterize chi u0R aR deltaR pair.2).2 hChi hDR]

private theorem fixedBucketDoubleFaultSurvivesGf2128_fin4_eq
    {chi u0L aL deltaL u0R aR deltaR : Tower128}
    (hChi : chi ≠ towerZero 7) (hDL : deltaL ≠ towerZero 7) (hDR : deltaR ≠ towerZero 7) :
    finSum 4 (fun i =>
      if fixedBucketDoubleFaultSurvivesGf2128 chi u0L aL deltaL u0R aR deltaR (boolPairSampleEnum.toFun i)
      then 1 else 0) = 1 := by
  have hCongr :
      finSum 4 (fun i =>
        if fixedBucketDoubleFaultSurvivesGf2128 chi u0L aL deltaL u0R aR deltaR (boolPairSampleEnum.toFun i)
        then 1 else 0) =
      finSum 4 (fun i => if i = (⟨0, by decide⟩ : Fin 4) then 1 else 0) := by
    apply finSum_congr
    intro i
    rw [fixedBucketDoubleFaultSurvivesGf2128_eq_both_false hChi hDL hDR]
    rcases i with ⟨v, hv⟩
    match v with
    | 0 =>
      have h : (⟨0, hv⟩ : Fin 4) = ⟨0, by decide⟩ := by apply Fin.ext; rfl
      rw [h]; decide
    | 1 =>
      have h : (⟨1, hv⟩ : Fin 4) = ⟨1, by decide⟩ := by apply Fin.ext; rfl
      rw [h]; decide
    | 2 =>
      have h : (⟨2, hv⟩ : Fin 4) = ⟨2, by decide⟩ := by apply Fin.ext; rfl
      rw [h]; decide
    | 3 =>
      have h : (⟨3, hv⟩ : Fin 4) = ⟨3, by decide⟩ := by apply Fin.ext; rfl
      rw [h]; decide
    | _ + 4 => exact False.elim (by omega)
  rw [hCongr, finSum_eq_indicator]

/-- **`#tooth` Fixed-Bucket `k + 2N` Selective-Abort Wire-Bit Leak Over `Tower128` (`tooth_fixed_bucket_selective_abort_leaks_wire_bit`)**:
    Under deterministic `(k, k + 2N)` combine without post-lock coin permutation, injecting nonzero
    `Tower128` OT faults `deltaL, deltaR ≠ 0` passes both algebraic `GF(2^128)` sacrifice checks in
    exact `1 / 4` of sessions (`finSum 4 = 1`) and reveals the honest online wire bit `y` with
    probability `1`! -/
theorem tooth_fixed_bucket_selective_abort_leaks_wire_bit
    {chi u0L aL deltaL u0R aR deltaR : Tower128}
    (hChi : chi ≠ towerZero 7) (hDL : deltaL ≠ towerZero 7) (hDR : deltaR ≠ towerZero 7) :
    ∃ survivalCount : Nat,
      survivalCount = finSum 4 (fun i =>
        if fixedBucketDoubleFaultSurvivesGf2128 chi u0L aL deltaL u0R aR deltaR (boolPairSampleEnum.toFun i)
        then 1 else 0) ∧
      survivalCount = 1 ∧
      ratLe (1, 4) (survivalCount, 4) ∧
      (∀ (sample : Bool × Bool) (y : Bool),
        fixedBucketDoubleFaultSurvivesGf2128 chi u0L aL deltaL u0R aR deltaR sample = true →
        onlineBeaverOpenBit y (combineBucketBit sample.1 sample.2) = y) ∧
      (∀ (sample : Bool × Bool),
        fixedBucketDoubleFaultSurvivesGf2128 chi u0L aL deltaL u0R aR deltaR sample = true →
        onlineBeaverOpenBit false (combineBucketBit sample.1 sample.2) ≠
          onlineBeaverOpenBit true (combineBucketBit sample.1 sample.2)) := by
  let survivalCount := finSum 4 (fun i =>
    if fixedBucketDoubleFaultSurvivesGf2128 chi u0L aL deltaL u0R aR deltaR (boolPairSampleEnum.toFun i)
    then 1 else 0)
  have hCount : survivalCount = 1 := fixedBucketDoubleFaultSurvivesGf2128_fin4_eq hChi hDL hDR
  refine ⟨survivalCount, rfl, hCount, ?_, ?_, ?_⟩
  · rw [hCount]
    exact ⟨by omega, by omega, Nat.le_refl 4⟩
  · intro ⟨b1, b2⟩ y hSurv
    dsimp only [fixedBucketDoubleFaultSurvivesGf2128] at hSurv
    rw [(otSacrificeCheckGf2128_characterize chi u0L aL deltaL b1).2 hChi hDL,
        (otSacrificeCheckGf2128_characterize chi u0R aR deltaR b2).2 hChi hDR] at hSurv
    cases b1 <;> cases b2
    · cases y <;> rfl
    · cases hSurv
    · cases hSurv
    · cases hSurv
  · intro ⟨b1, b2⟩ hSurv
    dsimp only [fixedBucketDoubleFaultSurvivesGf2128] at hSurv
    rw [(otSacrificeCheckGf2128_characterize chi u0L aL deltaL b1).2 hChi hDL,
        (otSacrificeCheckGf2128_characterize chi u0R aR deltaR b2).2 hChi hDR] at hSurv
    cases b1 <;> cases b2
    · decide
    · cases hSurv
    · cases hSurv
    · cases hSurv

private def finFind? : (n : Nat) → (Fin n → Bool) → Option (Fin n)
  | 0, _ => none
  | n + 1, p =>
    if p ⟨0, Nat.zero_lt_succ n⟩ then
      some ⟨0, Nat.zero_lt_succ n⟩
    else
      match finFind? n (fun j => p ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩) with
      | some j => some ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩
      | none => none

private theorem finFind?_spec : ∀ (n : Nat) (p : Fin n → Bool),
    match finFind? n p with
    | some idx => p idx = true
    | none => ∀ i : Fin n, p i = false
  | 0, _ => fun i => Fin.elim0 i
  | n + 1, p => by
    unfold finFind?
    cases hp0 : p ⟨0, Nat.zero_lt_succ n⟩
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have ih := finFind?_spec n (fun j => p ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩)
      cases hRec : finFind? n (fun j => p ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩) with
      | some j =>
        rw [hRec] at ih
        exact ih
      | none =>
        rw [hRec] at ih
        rintro ⟨v, hv⟩
        cases v with
        | zero => exact hp0
        | succ u => exact ih ⟨u, Nat.lt_of_succ_lt_succ hv⟩
    · simp only [↓reduceIte]
      exact hp0

private theorem finSum_unique_bool_le_one (k : Nat) (p : Fin k → Bool)
    (hUnique : ∀ a b : Fin k, p a = true → p b = true → a = b) :
    finSum k (fun c => if p c then 1 else 0) ≤ 1 := by
  have hSpec := finFind?_spec k p
  cases hFind : finFind? k p with
  | none =>
    rw [hFind] at hSpec
    dsimp only at hSpec
    have hCongr : finSum k (fun c => if p c then 1 else 0) = finSum k (fun _ => 0) := by
      apply finSum_congr
      intro c
      rw [hSpec c]
      rfl
    rw [hCongr, finSum_const]
    omega
  | some c₀ =>
    rw [hFind] at hSpec
    dsimp only at hSpec
    have hCongr : finSum k (fun c => if p c then 1 else 0) =
        finSum k (fun c => if c = c₀ then 1 else 0) := by
      apply finSum_congr
      intro c
      cases hpc : p c
      · have hcNe : c ≠ c₀ := fun hEq => by subst hEq; rw [hpc] at hSpec; cases hSpec
        rw [cIte_neg hcNe]
        rfl
      · have hcEq : c = c₀ := hUnique c c₀ hpc hSpec
        rw [cIte_pos hcEq]
        rfl
    rw [hCongr, finSum_eq_indicator]
    exact Nat.le_refl 1

/-- **Coin-Permuted Triple Bucketing Security & Double-Fault Bound Over `Tower128` (`coin_permuted_bucketing_hides_wire_and_bounds_double_fault`)**:
    1. Whenever at least one bucket partner is uncorrupted, `onlineBeaverOpenBit` is identically
       uniform over `bRight ∈ Fin 2` (`by mask_bijection_hop`), leaking `0` bits of `y`.
    2. Across a post-lock public coin permutation (`partnerOfI0 : Fin (2N - 1) → Fin (2N)` injective)
       and `Tower128` algebraic sacrifice checks (`otSacrificeCheckGf2128`), any 2-fault double-hit
       survives in at most `1` of `4 * (2N - 1)` joint outcomes (`≤ 1 / (4 * (2N - 1))`). -/
theorem coin_permuted_bucketing_hides_wire_and_bounds_double_fault
    {N : Nat} (hNPos : 1 ≤ N)
    {chi u0L aL deltaL u0R aR deltaR : Tower128}
    (hChi : chi ≠ towerZero 7) (hDL : deltaL ≠ towerZero 7) (hDR : deltaR ≠ towerZero 7)
    (i1 : Fin (2 * N))
    (partnerOfI0 : Fin (2 * N - 1) → Fin (2 * N))
    (hPartnerInj : Function.Injective partnerOfI0) :
    (∀ (y bLeft : Bool) (weight : Bool → Nat),
      finSum 2 (fun idx =>
        weight (onlineBeaverOpenBit y (combineBucketBit bLeft (boolSampleEnum.toFun idx)))) =
      finSum 2 (fun idx =>
        weight (boolSampleEnum.toFun idx))) ∧
    (let partnerHitCount := finSum (2 * N - 1) (fun c => if partnerOfI0 c == i1 then 1 else 0)
     let jointBadOutcomes := finSum 4 (fun s =>
       finSum (2 * N - 1) (fun c =>
         if fixedBucketDoubleFaultSurvivesGf2128 chi u0L aL deltaL u0R aR deltaR (boolPairSampleEnum.toFun s) &&
            (partnerOfI0 c == i1)
         then 1 else 0))
     partnerHitCount ≤ 1 ∧
     jointBadOutcomes ≤ 1 ∧
     ratLe (jointBadOutcomes, 4 * (2 * N - 1)) (1, 4 * (2 * N - 1))) := by
  refine ⟨?_, ?_⟩
  · intro y bLeft weight
    unfold onlineBeaverOpenBit combineBucketBit
    have hAssoc : ∀ idx : Fin 2,
        (y != (bLeft != boolSampleEnum.toFun idx)) = ((y != bLeft) != boolSampleEnum.toFun idx) :=
      fun idx => (bool_bne_assoc y bLeft (boolSampleEnum.toFun idx)).symm
    simp only [hAssoc]
    mask_bijection_hop (boolXorEquiv (y != bLeft))
  · intro partnerHitCount jointBadOutcomes
    have hHitLe : partnerHitCount ≤ 1 :=
      finSum_unique_bool_le_one (2 * N - 1) (fun c => partnerOfI0 c == i1)
        (fun c1 c2 hc1 hc2 => hPartnerInj ((eq_of_beq hc1).trans (eq_of_beq hc2).symm))
    have hSurvFalseAt : ∀ idx : Fin 4, idx ≠ ⟨0, by decide⟩ →
        fixedBucketDoubleFaultSurvivesGf2128 chi u0L aL deltaL u0R aR deltaR
          (boolPairSampleEnum.toFun idx) = false := by
      rintro ⟨v, hv⟩ hNe
      rw [@fixedBucketDoubleFaultSurvivesGf2128_eq_both_false chi u0L aL deltaL u0R aR deltaR hChi hDL hDR]
      match v with
      | 0 => exact False.elim (hNe (Fin.ext rfl))
      | 1 =>
        have hs : (⟨1, hv⟩ : Fin 4) = ⟨1, by decide⟩ := Fin.ext rfl
        rw [hs]; decide
      | 2 =>
        have hs : (⟨2, hv⟩ : Fin 4) = ⟨2, by decide⟩ := Fin.ext rfl
        rw [hs]; decide
      | 3 =>
        have hs : (⟨3, hv⟩ : Fin 4) = ⟨3, by decide⟩ := Fin.ext rfl
        rw [hs]; decide
      | _ + 4 => exact False.elim (by omega)
    have hJointLeInd :
        jointBadOutcomes ≤ finSum 4 (fun s => if s = (⟨0, by decide⟩ : Fin 4) then 1 else 0) := by
      apply finSum_le_finSum
      intro s
      if hs0 : s = ⟨0, by decide⟩ then
        subst hs0
        have hTrue : fixedBucketDoubleFaultSurvivesGf2128 chi u0L aL deltaL u0R aR deltaR
            (boolPairSampleEnum.toFun ⟨0, by decide⟩) = true := by
          rw [@fixedBucketDoubleFaultSurvivesGf2128_eq_both_false chi u0L aL deltaL u0R aR deltaR hChi hDL hDR]
          decide
        rw [cIte_pos rfl]
        have hEqHit : finSum (2 * N - 1) (fun c =>
            if fixedBucketDoubleFaultSurvivesGf2128 chi u0L aL deltaL u0R aR deltaR
                (boolPairSampleEnum.toFun ⟨0, by decide⟩) && (partnerOfI0 c == i1)
            then 1 else 0) = partnerHitCount := by
          apply finSum_congr
          intro c
          rw [hTrue, Bool.true_and]
        rw [hEqHit]
        exact hHitLe
      else
        have hFalse := hSurvFalseAt s hs0
        rw [cIte_neg hs0]
        have hZero : finSum (2 * N - 1) (fun c =>
            if fixedBucketDoubleFaultSurvivesGf2128 chi u0L aL deltaL u0R aR deltaR
                (boolPairSampleEnum.toFun s) && (partnerOfI0 c == i1)
            then 1 else 0) = finSum (2 * N - 1) (fun _ => 0) := by
          apply finSum_congr
          intro c
          rw [hFalse, Bool.false_and]
          rfl
        rw [hZero, finSum_const]
        omega
    rw [finSum_eq_indicator] at hJointLeInd
    have hDenPos : 0 < 4 * (2 * N - 1) := by omega
    exact ⟨hHitLe, hJointLeInd, ⟨hDenPos, hDenPos, Nat.mul_le_mul_right _ hJointLeInd⟩⟩

#tooth_pair
  Qsag.coin_permuted_bucketing_hides_wire_and_bounds_double_fault
  vs
  Qsag.tooth_fixed_bucket_selective_abort_leaks_wire_bit

/-! ## 6. `verify_all_pending` -> `all_outputs_zero` -> `PRECOMMIT` -> `FREEZE` Barrier, `InvalidTape` Conditional-Privacy & Multi-Turn `compose_forward_sim` -/

/-- Encoded residual in the transparent scalar test model; not a Rust curve or
    hashed-address ownership residual. -/
def circuitPkResidual (group : ScalarGroup) (pk : Fin group.orderNat) (s' : MigrationKey256) :
    MigrationKey256 :=
  (canonicalSubgroupHom group).encodePk (scalarMulKey (canonicalSubgroupHom group) s') ^^^
    (canonicalSubgroupHom group).encodePk pk

/-- Canonical-range and equality check for the transparent scalar test model.
    Hashed legacy addresses require the separate collision-aware relation below. -/
def circuitAllOutputsZero (group : ScalarGroup) (pk : Fin group.orderNat) (s' : MigrationKey256) : Bool :=
  requireCanonicalScalar group s' && (circuitPkResidual group pk s' == 0#256)

/-- On any canonical secret key `ks.secret`, `circuitAllOutputsZero` evaluates to `true` **iff**
    the net witness fault `delta` is `0#256` (zero unproved `Function.Injective pkOf` assumption!). -/
theorem circuitAllOutputsZero_iff_zero_fault
    (group : ScalarGroup) (ks : RssKeyShares3)
    (hCanon : requireCanonicalScalar group ks.secret = true)
    (delta : MigrationKey256) :
    let pk := scalarMulKey (canonicalSubgroupHom group) ks.secret
    let s' := ((ks.s0 ^^^ delta) ^^^ ks.s1) ^^^ ks.s2
    circuitAllOutputsZero group pk s' = true ↔ delta = 0#256 := by
  intro pk s'
  have hs'Eq : s' = ks.secret ^^^ delta := by
    dsimp only [s', RssKeyShares3.secret]; bv_xor_cancel
  unfold circuitAllOutputsZero circuitPkResidual
  rw [hs'Eq, Bool.and_eq_true, beq_iff_eq, bv_xor_eq_zero_iff]
  constructor
  · rintro ⟨hs'Canon, hEncEq⟩
    have hPtEq := (canonicalSubgroupHom group).encodePk_injective hEncEq
    have hKeyEq : ks.secret ^^^ delta = ks.secret :=
      (canonicalSubgroupHom_injective_on_canonical group).1 (ks.secret ^^^ delta) ks.secret hs'Canon hCanon hPtEq
    have hCancel := congrArg (ks.secret ^^^ ·) hKeyEq
    rw [bv_xor_cancel_left, bv_xor_self] at hCancel
    exact hCancel
  · rintro rfl
    rw [bv_xor_zero]
    exact ⟨hCanon, rfl⟩

/-- Upfront `Error::InvalidTape` predicate (`co_zk_mpc.rs:720-750`): folds `< domain.modulus`
    over PRG draws squeezed strictly from the reconstructed ZKBoo head tape seed
    `(seed0 ^^^ seed1) ^^^ seed2` (`QSAG.OUTER.SEED.V1`), independent of the witness `ks`! -/
def evalUpfrontTapeValidity (drawValidPred : MigrationKey256 → Bool)
    (seed0 seed1 seed2 : MigrationKey256) : Bool :=
  drawValidPred ((seed0 ^^^ seed1) ^^^ seed2)

/-- Constructive `SimpleEquiv` pad bijection on `BitVec 128` induced by BBCGGI19 base-case
    randomization `uBits ↦ packTower 7 (target + rb * unpackTower 7 uBits)` for `rb ≠ 0`
    (`outer_mpc.rs:2332-2350`). -/
def tower128BaseSacrificeEquiv (target rb : Tower128) (hRb : rb ≠ towerZero 7) :
    SimpleEquiv (BitVec 128) (BitVec 128) where
  toFun mBits := packTower 7 (towerAdd 7 target (towerMul 7 rb (unpackTower 7 mBits)))
  invFun yBits := packTower 7 (towerMul 7 (towerInv 7 rb) (towerAdd 7 target (unpackTower 7 yBits)))
  left_inv mBits := by
    rw [unpackTower_packTower, towerAdd_cancel,
        ← towerMul_assoc 7 (towerInv 7 rb) rb _,
        towerMul_comm 7 (towerInv 7 rb) rb,
        towerMul_inv 7 rb hRb,
        towerOne_mul,
        packTower_unpackTower]
  right_inv yBits := by
    rw [unpackTower_packTower,
        ← towerMul_assoc 7 rb (towerInv 7 rb) _,
        towerMul_inv 7 rb hRb,
        towerOne_mul,
        towerAdd_cancel,
        packTower_unpackTower]

/-- Observable tuple for a standalone masking experiment. It is not the full
    corrupt-party view of Rust execution: public inputs, initial knowledge, and
    failed multiplication-check transcripts are absent. -/
structure HardenedRssCeremonyView (ZkView : Type) where
  rssWitnessMine             : MigrationKey256
  rssWitnessNext             : MigrationKey256
  openedValidTape            : Bool
  bbcggiAlpha                : BitVec 128
  bbcggiBeta                 : BitVec 128
  bbcggiGamma                : BitVec 128
  openedAllOutputsZero       : Option Bool
  postPrecommitFreezePayload : Option (MigrationKey256 × ZkView)
  deriving Repr, DecidableEq

/-- Synthetic masking experiment using ideal scalar evaluation and tower
    multiplication. Despite the historical name, this does not execute the
    active protocol or either of its verification routines. -/
def realHardenedRssCeremonyView {ZkView : Type}
    (group : ScalarGroup)
    (drawValidPred : MigrationKey256 → Bool)
    (zkCommit : MigrationKey256 → ZkView)
    (ks : RssKeyShares3) (delta : MigrationKey256)
    (seed0 seed1 seed2 : MigrationKey256)
    (aFin bFin rb : Tower128)
    (pads : MigrationKey256 × (BitVec 128 × BitVec 128)) :
    HardenedRssCeremonyView ZkView :=
  let pk := scalarMulKey (canonicalSubgroupHom group) ks.secret
  let s1Fresh := ks.s1 ^^^ pads.1
  let s2Fresh := ks.s2 ^^^ pads.1
  let s' := ((ks.s0 ^^^ delta) ^^^ s1Fresh) ^^^ s2Fresh
  let validTape := evalUpfrontTapeValidity drawValidPred seed0 seed1 seed2
  let alpha := packTower 7 (towerAdd 7 aFin (towerMul 7 rb (unpackTower 7 pads.2.1)))
  let beta  := packTower 7 (towerAdd 7 bFin (towerMul 7 rb (unpackTower 7 pads.2.2)))
  if !validTape then
    { rssWitnessMine := ks.s0 ^^^ delta
      rssWitnessNext := s1Fresh
      openedValidTape := false
      bbcggiAlpha := 0#128
      bbcggiBeta := 0#128
      bbcggiGamma := 0#128
      openedAllOutputsZero := none
      postPrecommitFreezePayload := none }
  else
    let allZero := circuitAllOutputsZero group pk s'
    { rssWitnessMine := ks.s0 ^^^ delta
      rssWitnessNext := s1Fresh
      openedValidTape := true
      bbcggiAlpha := alpha
      bbcggiBeta := beta
      bbcggiGamma := mulExec 7 alpha beta
      openedAllOutputsZero := some allZero
      postPrecommitFreezePayload :=
        if allZero then some (circuitPkResidual group pk s', zkCommit s') else none }

/-- Ideal `ks.secret`-free simulator for witness-fault aborts: takes **only** custodian `0`'s own
    submitted share `s0Submitted := ks.s0 ^^^ delta`, `validTape`, and uniform pads! -/
@[expose] def simHardenedAbortView (ZkView : Type)
    (s0Submitted : MigrationKey256) (validTape : Bool)
    (pads : MigrationKey256 × (BitVec 128 × BitVec 128)) :
    HardenedRssCeremonyView ZkView :=
  if !validTape then
    { rssWitnessMine := s0Submitted
      rssWitnessNext := pads.1
      openedValidTape := false
      bbcggiAlpha := 0#128
      bbcggiBeta := 0#128
      bbcggiGamma := 0#128
      openedAllOutputsZero := none
      postPrecommitFreezePayload := none }
  else
    { rssWitnessMine := s0Submitted
      rssWitnessNext := pads.1
      openedValidTape := true
      bbcggiAlpha := pads.2.1
      bbcggiBeta := pads.2.2
      bbcggiGamma := mulExec 7 pads.2.1 pads.2.2
      openedAllOutputsZero := some false
      postPrecommitFreezePayload := none }

/-- Single-experiment masking equality for the synthetic tower/scalar view.
    The explicit uniform-pad enumeration is essential. This is not a simulation
    of the actual multi-round migration protocol or its initial adversary view. -/
theorem hardened_co_zk_mpc_zero_test_hides_secret_on_input_fault
    {C : Nat} {ZkView : Type}
    (group : ScalarGroup)
    (drawValidPred : MigrationKey256 → Bool)
    (zkCommit : MigrationKey256 → ZkView)
    (ks : RssKeyShares3) (hCanon : requireCanonicalScalar group ks.secret = true)
    (delta : MigrationKey256) (hFault : delta ≠ 0#256)
    (seed0 seed1 seed2 : MigrationKey256)
    (aFin bFin rb : Tower128) (hRb : rb ≠ towerZero 7)
    (enum : SimpleEquiv (Fin C) (MigrationKey256 × (BitVec 128 × BitVec 128)))
    (weight : HardenedRssCeremonyView ZkView → Nat) :
    finSum C (fun i =>
      weight (realHardenedRssCeremonyView group drawValidPred zkCommit ks delta
        seed0 seed1 seed2 aFin bFin rb (enum.toFun i))) =
    finSum C (fun i =>
      weight (simHardenedAbortView ZkView (ks.s0 ^^^ delta)
        (evalUpfrontTapeValidity drawValidPred seed0 seed1 seed2) (enum.toFun i))) := by
  have hFreshCandidate : ∀ r : MigrationKey256,
      ((ks.s0 ^^^ delta) ^^^ (ks.s1 ^^^ r)) ^^^ (ks.s2 ^^^ r) =
      ((ks.s0 ^^^ delta) ^^^ ks.s1) ^^^ ks.s2 := by
    intro r; bv_xor_cancel
  have hAllZeroFalse :
      circuitAllOutputsZero group (scalarMulKey (canonicalSubgroupHom group) ks.secret)
        (((ks.s0 ^^^ delta) ^^^ ks.s1) ^^^ ks.s2) = false := by
    cases h : circuitAllOutputsZero group (scalarMulKey (canonicalSubgroupHom group) ks.secret)
        (((ks.s0 ^^^ delta) ^^^ ks.s1) ^^^ ks.s2)
    · rfl
    · exfalso
      exact hFault ((circuitAllOutputsZero_iff_zero_fault group ks hCanon delta).mp h)
  let padEquiv : SimpleEquiv (MigrationKey256 × (BitVec 128 × BitVec 128))
      (MigrationKey256 × (BitVec 128 × BitVec 128)) :=
    SimpleEquiv.prodCongr (bvXorEquiv ks.s1)
      (SimpleEquiv.prodCongr
        (SimpleEquiv.symm (tower128BaseSacrificeEquiv aFin rb hRb))
        (SimpleEquiv.symm (tower128BaseSacrificeEquiv bFin rb hRb)))
  apply finSum_bijection_hop_eq enum padEquiv
    (fun p => weight (realHardenedRssCeremonyView group drawValidPred zkCommit ks delta
      seed0 seed1 seed2 aFin bFin rb p))
    (fun p => weight (simHardenedAbortView ZkView (ks.s0 ^^^ delta)
      (evalUpfrontTapeValidity drawValidPred seed0 seed1 seed2) p))
  rintro ⟨rPad, uPad, vPad⟩
  unfold realHardenedRssCeremonyView simHardenedAbortView
  dsimp only [padEquiv, SimpleEquiv.prodCongr, SimpleEquiv.symm, bvXorEquiv]
  have hrCancel : ks.s1 ^^^ (rPad ^^^ ks.s1) = rPad := by bv_xor_cancel
  have huCancel : packTower 7 (towerAdd 7 aFin (towerMul 7 rb
      (unpackTower 7 ((tower128BaseSacrificeEquiv aFin rb hRb).invFun uPad)))) = uPad :=
    (tower128BaseSacrificeEquiv aFin rb hRb).right_inv uPad
  have hvCancel : packTower 7 (towerAdd 7 bFin (towerMul 7 rb
      (unpackTower 7 ((tower128BaseSacrificeEquiv bFin rb hRb).invFun vPad)))) = vPad :=
    (tower128BaseSacrificeEquiv bFin rb hRb).right_inv vPad
  rw [hFreshCandidate (rPad ^^^ ks.s1), hrCancel]
  cases evalUpfrontTapeValidity drawValidPred seed0 seed1 seed2
  · simp
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hAllZeroFalse, huCancel, hvCancel]

#tooth_pair
  Qsag.hardened_co_zk_mpc_zero_test_hides_secret_on_input_fault
  vs
  Qsag.tooth_premature_residual_open_recovers_spending_key

private theorem natAbsDiff_finSum_indicator_self {C : Nat} (p : Fin C → Bool) :
    natAbsDiff (finSum C (fun i => if p i then 1 else 0))
               (finSum C (fun i => if p i then 1 else 0)) = 0 := by
  have hLe := finSum_indicator_diff_le p p (fun _ => false) (fun _ _ => rfl)
  simp only [Bool.false_eq_true, ↓reduceIte, finSum_const, Nat.mul_zero] at hLe
  exact Nat.eq_zero_of_le_zero hLe

/-- Zero distinguishing advantage (`natAbsDiff = 0`) between ANY two canonical spending keys
    `ksA, ksB` sharing custodian `0`'s local share (`ksA.s0 = ksB.s0`) on any nonzero fault `delta ≠ 0#256`. -/
theorem hardened_co_zk_mpc_two_keys_zero_advantage_on_fault
    {C : Nat} {ZkView : Type}
    (group : ScalarGroup)
    (drawValidPred : MigrationKey256 → Bool)
    (zkCommit : MigrationKey256 → ZkView)
    (ksA ksB : RssKeyShares3) (hSameS0 : ksA.s0 = ksB.s0)
    (hCanonA : requireCanonicalScalar group ksA.secret = true)
    (hCanonB : requireCanonicalScalar group ksB.secret = true)
    (delta : MigrationKey256) (hFault : delta ≠ 0#256)
    (seed0 seed1 seed2 : MigrationKey256)
    (aFinA bFinA aFinB bFinB rb : Tower128) (hRb : rb ≠ towerZero 7)
    (enum : SimpleEquiv (Fin C) (MigrationKey256 × (BitVec 128 × BitVec 128)))
    (D : HardenedRssCeremonyView ZkView → Bool) :
    natAbsDiff
      (finSum C (fun i =>
        if D (realHardenedRssCeremonyView group drawValidPred zkCommit ksA delta
          seed0 seed1 seed2 aFinA bFinA rb (enum.toFun i))
        then 1 else 0))
      (finSum C (fun i =>
        if D (realHardenedRssCeremonyView group drawValidPred zkCommit ksB delta
          seed0 seed1 seed2 aFinB bFinB rb (enum.toFun i))
        then 1 else 0)) = 0 := by
  let wFn : HardenedRssCeremonyView ZkView → Nat := fun v => if D v then 1 else 0
  have hA := hardened_co_zk_mpc_zero_test_hides_secret_on_input_fault
    group drawValidPred zkCommit ksA hCanonA delta hFault seed0 seed1 seed2 aFinA bFinA rb hRb enum wFn
  have hB := hardened_co_zk_mpc_zero_test_hides_secret_on_input_fault
    group drawValidPred zkCommit ksB hCanonB delta hFault seed0 seed1 seed2 aFinB bFinB rb hRb enum wFn
  dsimp only [wFn] at hA hB
  rw [hA, hB, hSameS0]
  exact natAbsDiff_finSum_indicator_self _

/-- **Upfront `Error::InvalidTape` Conditional-Privacy Theorem (`upfront_invalid_tape_independent_of_spending_key`)**:
    1. `evalUpfrontTapeValidity` (`co_zk_mpc.rs:743-750`) depends solely on `(seed0, seed1, seed2)`
       and `0` bits of `ks.secret`; under uniform honest `QSAG.OUTER.SEED.V1` share `seed2`, the
       distribution of `evalUpfrontTapeValidity` is invariant under ANY adaptive `seed0'` chosen by
       corrupt custodian `0` (`by mask_bijection_hop`) — preventing selective `InvalidTape` bias!
    2. Whenever `evalUpfrontTapeValidity = false` (`InvalidTape` upfront abort before `PRECOMMIT`),
       corrupt custodian `0`'s ceremony view has **zero** distinguishing advantage between `ksA` and
       `ksB`, **even when `delta = 0#256`**! -/
theorem upfront_invalid_tape_independent_of_spending_key
    {Cs C : Nat} {ZkView : Type}
    (group : ScalarGroup)
    (drawValidPred : MigrationKey256 → Bool)
    (zkCommit : MigrationKey256 → ZkView)
    (seed0' seed1 : MigrationKey256)
    (enumSeed : SimpleEquiv (Fin Cs) MigrationKey256)
    (enumPads : SimpleEquiv (Fin C) (MigrationKey256 × (BitVec 128 × BitVec 128))) :
    (∀ weightBool : Bool → Nat,
      finSum Cs (fun i =>
        weightBool (evalUpfrontTapeValidity drawValidPred seed0' seed1 (enumSeed.toFun i))) =
      finSum Cs (fun i =>
        weightBool (drawValidPred (enumSeed.toFun i)))) ∧
    (∀ (ksA ksB : RssKeyShares3) (delta seed2 : MigrationKey256)
       (aFinA bFinA aFinB bFinB rb : Tower128)
       (D : HardenedRssCeremonyView ZkView → Bool),
      ksA.s0 = ksB.s0 →
      evalUpfrontTapeValidity drawValidPred seed0' seed1 seed2 = false →
      natAbsDiff
        (finSum C (fun i =>
          if D (realHardenedRssCeremonyView group drawValidPred zkCommit ksA delta
            seed0' seed1 seed2 aFinA bFinA rb (enumPads.toFun i))
          then 1 else 0))
        (finSum C (fun i =>
          if D (realHardenedRssCeremonyView group drawValidPred zkCommit ksB delta
            seed0' seed1 seed2 aFinB bFinB rb (enumPads.toFun i))
          then 1 else 0)) = 0) := by
  refine ⟨?_, ?_⟩
  · intro weightBool
    unfold evalUpfrontTapeValidity
    mask_bijection_hop (bvXorEquiv (seed0' ^^^ seed1))
  · intro ksA ksB delta seed2 aFinA bFinA aFinB bFinB rb D hSameS0 hInvalid
    let wFn : HardenedRssCeremonyView ZkView → Nat := fun v => if D v then 1 else 0
    have hSimA :
        finSum C (fun i =>
          wFn (realHardenedRssCeremonyView group drawValidPred zkCommit ksA delta
            seed0' seed1 seed2 aFinA bFinA rb (enumPads.toFun i))) =
        finSum C (fun i =>
          wFn (simHardenedAbortView ZkView (ksA.s0 ^^^ delta) false (enumPads.toFun i))) := by
      unfold realHardenedRssCeremonyView simHardenedAbortView
      simp only [hInvalid, Bool.not_false, ↓reduceIte]
      mask_bijection_hop (SimpleEquiv.prodCongr (bvXorEquiv ksA.s1) (SimpleEquiv.refl _))
    have hSimB :
        finSum C (fun i =>
          wFn (realHardenedRssCeremonyView group drawValidPred zkCommit ksB delta
            seed0' seed1 seed2 aFinB bFinB rb (enumPads.toFun i))) =
        finSum C (fun i =>
          wFn (simHardenedAbortView ZkView (ksB.s0 ^^^ delta) false (enumPads.toFun i))) := by
      unfold realHardenedRssCeremonyView simHardenedAbortView
      simp only [hInvalid, Bool.not_false, ↓reduceIte]
      mask_bijection_hop (SimpleEquiv.prodCongr (bvXorEquiv ksB.s1) (SimpleEquiv.refl _))
    dsimp only [wFn] at hSimA hSimB
    rw [hSimA, hSimB, hSameS0]
    exact natAbsDiff_finSum_indicator_self _

/-- Buggy upfront check that prematurely folds `requireCanonicalScalar(witness)` into the upfront
    `Error::InvalidTape` open before `PRECOMMIT` / `all_outputs_zero`. -/
def buggyUpfrontTapeAndWitnessCheck {ZkView : Type}
    (group : ScalarGroup)
    (drawValidPred : MigrationKey256 → Bool)
    (zkCommit : MigrationKey256 → ZkView)
    (ks : RssKeyShares3) (delta : MigrationKey256)
    (seed0 seed1 seed2 : MigrationKey256) :
    Except CeremonyAbortError ZkView :=
  let pk := scalarMulKey (canonicalSubgroupHom group) ks.secret
  let s' := ((ks.s0 ^^^ delta) ^^^ ks.s1) ^^^ ks.s2
  let validUpfront := evalUpfrontTapeValidity drawValidPred seed0 seed1 seed2 &&
    requireCanonicalScalar group s'
  if !validUpfront then
    .error .invalidTape
  else if circuitPkResidual group pk s' != 0#256 then
    .error .invalidProof
  else
    .ok (zkCommit s')

/-- **`#tooth` Folding `requireCanonicalScalar` Into Upfront `InvalidTape` Leaks Secret Range Bits (`tooth_premature_witness_range_in_invalid_tape_leaks_secret_bit`)**:
    If a buggy implementation combined `requireCanonicalScalar .Secp256k1 s'` into the upfront
    `InvalidTape` check before `PRECOMMIT`, a single aborted 1-bit fault `delta = 2^255` on valid
    tapes returns `.error .invalidTape` on canonical key `sLow = SECP_N - 2^255` (`< 2^255`) vs.
    `.error .invalidProof` on canonical key `sHigh = 2^255 + 1` (`> 2^255`), leaking secret range
    bits in `1` query! -/
theorem tooth_premature_witness_range_in_invalid_tape_leaks_secret_bit
    {ZkView : Type} (zkCommit : MigrationKey256 → ZkView) :
    ∃ (ksLow ksHigh : RssKeyShares3) (delta : MigrationKey256),
      ksLow.s0 = ksHigh.s0 ∧
      requireCanonicalScalar .Secp256k1 ksLow.secret = true ∧
      requireCanonicalScalar .Secp256k1 ksHigh.secret = true ∧
      buggyUpfrontTapeAndWitnessCheck .Secp256k1 (fun _ => true) zkCommit ksLow delta 0#256 0#256 0#256 =
        .error .invalidTape ∧
      buggyUpfrontTapeAndWitnessCheck .Secp256k1 (fun _ => true) zkCommit ksHigh delta 0#256 0#256 0#256 =
        .error .invalidProof ∧
      buggyUpfrontTapeAndWitnessCheck .Secp256k1 (fun _ => true) zkCommit ksLow delta 0#256 0#256 0#256 ≠
        buggyUpfrontTapeAndWitnessCheck .Secp256k1 (fun _ => true) zkCommit ksHigh delta 0#256 0#256 0#256 := by
  let sLow : MigrationKey256 := BitVec.ofNat 256 (SECP256K1_ORDER_N - 2 ^ 255)
  let sHigh : MigrationKey256 := BitVec.ofNat 256 (2 ^ 255 + 1)
  let ksLow : RssKeyShares3 := ⟨0#256, sLow, 0#256⟩
  let ksHigh : RssKeyShares3 := ⟨0#256, sHigh, 0#256⟩
  let delta : MigrationKey256 := BitVec.ofNat 256 (2 ^ 255)
  have hSecLow : ksLow.secret = sLow := by dsimp [ksLow, RssKeyShares3.secret]; bv_xor_cancel
  have hSecHigh : ksHigh.secret = sHigh := by dsimp [ksHigh, RssKeyShares3.secret]; bv_xor_cancel
  have hCanonLow : requireCanonicalScalar .Secp256k1 sLow = true := by
    unfold requireCanonicalScalar ScalarGroup.orderNat SECP256K1_ORDER_N
    dsimp [sLow]
    decide
  have hCanonHigh : requireCanonicalScalar .Secp256k1 sHigh = true := by
    unfold requireCanonicalScalar ScalarGroup.orderNat SECP256K1_ORDER_N
    dsimp [sHigh]
    decide
  have hLowCandNotCanon :
      requireCanonicalScalar .Secp256k1 (((0#256 ^^^ delta) ^^^ sLow) ^^^ 0#256) = false := by
    have hSimp : (((0#256 ^^^ delta) ^^^ sLow) ^^^ 0#256) = delta ^^^ sLow := by bv_xor_cancel
    rw [hSimp]
    unfold requireCanonicalScalar ScalarGroup.orderNat SECP256K1_ORDER_N
    dsimp [sLow, delta]
    decide
  have hHighCandCanon :
      requireCanonicalScalar .Secp256k1 (((0#256 ^^^ delta) ^^^ sHigh) ^^^ 0#256) = true := by
    have hSimp : (((0#256 ^^^ delta) ^^^ sHigh) ^^^ 0#256) = delta ^^^ sHigh := by bv_xor_cancel
    rw [hSimp]
    unfold requireCanonicalScalar ScalarGroup.orderNat SECP256K1_ORDER_N
    dsimp [sHigh, delta]
    decide
  have hHighResNe :
      (circuitPkResidual .Secp256k1
        (scalarMulKey (canonicalSubgroupHom .Secp256k1) ksHigh.secret)
        (((0#256 ^^^ delta) ^^^ sHigh) ^^^ 0#256) != 0#256) = true := by
    rw [bne_iff_ne]
    intro hZero
    have hDeltaNe : delta ≠ 0#256 := by dsimp [delta]; decide
    have hAllZero : circuitAllOutputsZero .Secp256k1
        (scalarMulKey (canonicalSubgroupHom .Secp256k1) ksHigh.secret)
        (((ksHigh.s0 ^^^ delta) ^^^ ksHigh.s1) ^^^ ksHigh.s2) = true := by
      unfold circuitAllOutputsZero
      rw [Bool.and_eq_true, beq_iff_eq]
      exact ⟨hHighCandCanon, hZero⟩
    exact hDeltaNe ((circuitAllOutputsZero_iff_zero_fault .Secp256k1 ksHigh
      (by rw [hSecHigh]; exact hCanonHigh) delta).mp hAllZero)
  have hEvalLow :
      buggyUpfrontTapeAndWitnessCheck .Secp256k1 (fun _ => true) zkCommit ksLow delta 0#256 0#256 0#256 =
        .error .invalidTape := by
    unfold buggyUpfrontTapeAndWitnessCheck evalUpfrontTapeValidity
    dsimp only [ksLow]
    rw [hLowCandNotCanon]
    rfl
  have hEvalHigh :
      buggyUpfrontTapeAndWitnessCheck .Secp256k1 (fun _ => true) zkCommit ksHigh delta 0#256 0#256 0#256 =
        .error .invalidProof := by
    unfold buggyUpfrontTapeAndWitnessCheck evalUpfrontTapeValidity
    dsimp only [ksHigh]
    rw [hHighCandCanon, hHighResNe]
    rfl
  refine ⟨ksLow, ksHigh, delta, rfl, by rw [hSecLow]; exact hCanonLow, by rw [hSecHigh]; exact hCanonHigh,
    hEvalLow, hEvalHigh, ?_⟩
  rw [hEvalLow, hEvalHigh]
  intro hEq
  injection hEq with hErr
  cases hErr

#tooth_pair
  Qsag.upfront_invalid_tape_independent_of_spending_key
  vs
  Qsag.tooth_premature_witness_range_in_invalid_tape_leaks_secret_bit

/-! ## 7. Multi-Turn 3-Party RSS + BBCGGI19 + `all_outputs_zero` State Machine & `compose_forward_sim` -/

/-- Complete per-ceremony turn input exercising all four active outer-MPC barriers:
    1. `laneMask`: 64-lane uniformity (`isUniformLaneWord`),
    2. `seed0, seed1, seed2`: upfront `InvalidTape` (`evalUpfrontTapeValidity`),
    3. `maskTriple, mulTriples, mulChallenge`: `GF(2^128)` BBCGGI19 (`verifyAllPendingGf2128`),
    4. `deltaScalar`: witness fault tested by `circuitAllOutputsZero` before `PRECOMMIT`/`FREEZE`. -/
structure RssCeremonyTurnInput where
  deltaScalar  : MigrationKey256
  laneMask     : UInt64
  seed0        : MigrationKey256
  seed1        : MigrationKey256
  seed2        : MigrationKey256
  maskTriple   : Gf2128MulTriple
  mulTriples   : List Gf2128MulTriple
  mulChallenge : Tower128
  deriving DecidableEq

/-- Persistent concrete 3-share RSS custodian state across unbounded multi-turn executions. -/
structure ConcreteCustodianState where
  group     : ScalarGroup
  shares    : RssKeyShares3
  completed : Nat
  aborted   : Nat
  deriving Repr, DecidableEq

/-- Abstract single-secret custodian state after folding 3-party RSS shares. -/
structure AbstractCustodianState where
  group     : ScalarGroup
  secret    : MigrationKey256
  completed : Nat
  aborted   : Nat
  deriving Repr, DecidableEq

/-- Historical ideal arithmetic machine with independent preconditions.
    Despite the compatibility name, it does not execute malicious shared gates.
    MigrationExecution.run evaluates a linked gate trace instead. -/
def concreteCustodianMachine {ZkView : Type}
    (drawValidPred : MigrationKey256 → Bool)
    (zkCommit : MigrationKey256 → ZkView) :
    PartyMachine ConcreteCustodianState RssCeremonyTurnInput ZkView where
  step st inp :=
    let pk := scalarMulKey (canonicalSubgroupHom st.group) st.shares.secret
    let s' := ((st.shares.s0 ^^^ inp.deltaScalar) ^^^ st.shares.s1) ^^^ st.shares.s2
    let preGatesOk :=
      isUniformLaneWord inp.laneMask &&
      evalUpfrontTapeValidity drawValidPred inp.seed0 inp.seed1 inp.seed2 &&
      verifyAllPendingGf2128 inp.maskTriple inp.mulTriples inp.mulChallenge
    if !(preGatesOk && circuitAllOutputsZero st.group pk s') then
      none
    else
      some ({ st with completed := st.completed + 1 }, zkCommit s')
  errStep st _ := { st with aborted := st.aborted + 1 }

/-- Layer 2: Intermediate barrier-gate `PartyMachine` operating over `st.secret ^^^ inp.deltaScalar`. -/
def residualGateMachine {ZkView : Type}
    (drawValidPred : MigrationKey256 → Bool)
    (zkCommit : MigrationKey256 → ZkView) :
    PartyMachine AbstractCustodianState RssCeremonyTurnInput ZkView where
  step st inp :=
    let pk := scalarMulKey (canonicalSubgroupHom st.group) st.secret
    let s' := st.secret ^^^ inp.deltaScalar
    let preGatesOk :=
      isUniformLaneWord inp.laneMask &&
      evalUpfrontTapeValidity drawValidPred inp.seed0 inp.seed1 inp.seed2 &&
      verifyAllPendingGf2128 inp.maskTriple inp.mulTriples inp.mulChallenge
    if !(preGatesOk && circuitAllOutputsZero st.group pk s') then
      none
    else
      some ({ st with completed := st.completed + 1 }, zkCommit s')
  errStep st _ := { st with aborted := st.aborted + 1 }

/-- Layer 3: Ideal canonical zero-fault functionality accepting **iff** all pre-gates pass AND
    `inp.deltaScalar == 0#256`, releasing `zkCommit st.secret`. -/
def idealZeroFaultMachine {ZkView : Type}
    (drawValidPred : MigrationKey256 → Bool)
    (zkCommit : MigrationKey256 → ZkView) :
    PartyMachine AbstractCustodianState RssCeremonyTurnInput ZkView where
  step st inp :=
    let preGatesOk :=
      isUniformLaneWord inp.laneMask &&
      evalUpfrontTapeValidity drawValidPred inp.seed0 inp.seed1 inp.seed2 &&
      verifyAllPendingGf2128 inp.maskTriple inp.mulTriples inp.mulChallenge
    if !(preGatesOk && (inp.deltaScalar == 0#256)) then
      none
    else
      some ({ st with completed := st.completed + 1 }, zkCommit st.secret)
  errStep st _ := { st with aborted := st.aborted + 1 }

/-- `LockstepSim` from Layer 1 (`concreteCustodianMachine`) to Layer 2 (`residualGateMachine`). -/
def custodian_to_residualGate_lockstep {ZkView : Type}
    (drawValidPred : MigrationKey256 → Bool)
    (zkCommit : MigrationKey256 → ZkView) :
    LockstepSim
      (concreteCustodianMachine drawValidPred zkCommit)
      (residualGateMachine drawValidPred zkCommit) where
  Inv _ := True
  abs st :=
    { group := st.group
      secret := st.shares.secret
      completed := st.completed
      aborted := st.aborted }
  step_eq {st} inp _ := by
    have hShift : ((st.shares.s0 ^^^ inp.deltaScalar) ^^^ st.shares.s1) ^^^ st.shares.s2 =
        st.shares.secret ^^^ inp.deltaScalar := by
      unfold RssKeyShares3.secret; bv_xor_cancel
    dsimp only [concreteCustodianMachine, residualGateMachine]
    rw [hShift]
    cases (isUniformLaneWord inp.laneMask &&
      evalUpfrontTapeValidity drawValidPred inp.seed0 inp.seed1 inp.seed2 &&
      verifyAllPendingGf2128 inp.maskTriple inp.mulTriples inp.mulChallenge &&
      circuitAllOutputsZero st.group
        (scalarMulKey (canonicalSubgroupHom st.group) st.shares.secret)
        (st.shares.secret ^^^ inp.deltaScalar))
    · exact ⟨trivial, rfl, rfl⟩
    · exact ⟨trivial, rfl⟩

private theorem residualGate_step_eq_ideal {ZkView : Type}
    (drawValidPred : MigrationKey256 → Bool)
    (zkCommit : MigrationKey256 → ZkView)
    (s : AbstractCustodianState)
    (hCanon : requireCanonicalScalar s.group s.secret = true)
    (inp : RssCeremonyTurnInput) :
    (residualGateMachine drawValidPred zkCommit).step s inp =
      (idealZeroFaultMachine drawValidPred zkCommit).step s inp := by
  dsimp only [residualGateMachine, idealZeroFaultMachine]
  let ksSynth : RssKeyShares3 := ⟨0#256, s.secret, 0#256⟩
  have hSecEq : ksSynth.secret = s.secret := by dsimp [ksSynth, RssKeyShares3.secret]; bv_xor_cancel
  have hCandEq : ((ksSynth.s0 ^^^ inp.deltaScalar) ^^^ ksSynth.s1) ^^^ ksSynth.s2 =
      s.secret ^^^ inp.deltaScalar := by dsimp [ksSynth]; bv_xor_cancel
  have hIff := circuitAllOutputsZero_iff_zero_fault s.group ksSynth (by rw [hSecEq]; exact hCanon) inp.deltaScalar
  dsimp only at hIff
  rw [hSecEq, hCandEq] at hIff
  have hGateIff :
      circuitAllOutputsZero s.group
        (scalarMulKey (canonicalSubgroupHom s.group) s.secret)
        (s.secret ^^^ inp.deltaScalar) = (inp.deltaScalar == 0#256) := by
    cases hEq : (inp.deltaScalar == 0#256)
    · cases hZ : circuitAllOutputsZero s.group
          (scalarMulKey (canonicalSubgroupHom s.group) s.secret) (s.secret ^^^ inp.deltaScalar)
      · rfl
      · exfalso
        have hd0 := hIff.mp hZ
        rw [hd0] at hEq
        cases hEq
    · exact hIff.mpr (eq_of_beq hEq)
  rw [hGateIff]
  cases (isUniformLaneWord inp.laneMask &&
    evalUpfrontTapeValidity drawValidPred inp.seed0 inp.seed1 inp.seed2 &&
    verifyAllPendingGf2128 inp.maskTriple inp.mulTriples inp.mulChallenge) <;>
    cases hD : (inp.deltaScalar == 0#256)
  · rfl
  · rfl
  · rfl
  · rw [eq_of_beq hD, bv_xor_zero]

/-- `ForwardSim` from Layer 2 (`residualGateMachine`) to Layer 3 (`idealZeroFaultMachine`),
    preserving `requireCanonicalScalar st.group st.secret = true` across every transition. -/
def residualGate_to_ideal_forwardSim {ZkView : Type}
    (drawValidPred : MigrationKey256 → Bool)
    (zkCommit : MigrationKey256 → ZkView) :
    ForwardSim
      (residualGateMachine drawValidPred zkCommit)
      (idealZeroFaultMachine drawValidPred zkCommit) where
  Rel s₁ s₂ := s₁ = s₂ ∧ requireCanonicalScalar s₁.group s₁.secret = true
  sim_ok {s₁ s₁' s₂ inp out} hRel hStep := by
    rcases hRel with ⟨rfl, hCanon⟩
    rw [residualGate_step_eq_ideal drawValidPred zkCommit s₁ hCanon inp] at hStep
    rw [hStep]
    have hPres : s₁'.group = s₁.group ∧ s₁'.secret = s₁.secret := by
      dsimp only [idealZeroFaultMachine] at hStep
      cases hCond : (isUniformLaneWord inp.laneMask &&
        evalUpfrontTapeValidity drawValidPred inp.seed0 inp.seed1 inp.seed2 &&
        verifyAllPendingGf2128 inp.maskTriple inp.mulTriples inp.mulChallenge &&
        (inp.deltaScalar == 0#256))
      · rw [hCond] at hStep
        cases hStep
      · rw [hCond] at hStep
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte,
          Option.some.injEq, Prod.mk.injEq] at hStep
        rcases hStep with ⟨rfl, _⟩
        exact ⟨rfl, rfl⟩
    rw [hPres.1, hPres.2]
    exact ⟨rfl, rfl, hCanon⟩
  sim_err {s₁ s₂ inp} hRel hNone := by
    rcases hRel with ⟨rfl, hCanon⟩
    rw [residualGate_step_eq_ideal drawValidPred zkCommit s₁ hCanon inp] at hNone
    exact ⟨hNone, rfl, hCanon⟩

/-- End-to-end 3-layer `ForwardSim` spine synthesized in one line via `by compose_forward_sim`! -/
def custodian_to_ideal_spine {ZkView : Type}
    (drawValidPred : MigrationKey256 → Bool)
    (zkCommit : MigrationKey256 → ZkView) :
    ForwardSim
      (concreteCustodianMachine drawValidPred zkCommit)
      (idealZeroFaultMachine drawValidPred zkCommit) := by
  have h1 := custodian_to_residualGate_lockstep drawValidPred zkCommit
  have h2 := residualGate_to_ideal_forwardSim drawValidPred zkCommit
  compose_forward_sim

/-- Explicit bracket syntax witness for `compose_forward_sim [h1, h2]`. -/
def custodian_to_ideal_spine_explicit {ZkView : Type}
    (drawValidPred : MigrationKey256 → Bool)
    (zkCommit : MigrationKey256 → ZkView) :
    ForwardSim
      (concreteCustodianMachine drawValidPred zkCommit)
      (idealZeroFaultMachine drawValidPred zkCommit) := by
  compose_forward_sim [
    custodian_to_residualGate_lockstep drawValidPred zkCommit,
    residualGate_to_ideal_forwardSim drawValidPred zkCommit
  ]

private theorem idealZeroFault_trace_inv {ZkView : Type}
    (drawValidPred : MigrationKey256 → Bool)
    (zkCommit : MigrationKey256 → ZkView)
    {s₀ s_f : AbstractCustodianState} {tr : List (RssCeremonyTurnInput × ZkView)}
    (hTrace : (idealZeroFaultMachine drawValidPred zkCommit).ValidTrace s₀ tr s_f) :
    ∀ p ∈ tr,
      isUniformLaneWord p.1.laneMask = true ∧
      evalUpfrontTapeValidity drawValidPred p.1.seed0 p.1.seed1 p.1.seed2 = true ∧
      verifyAllPendingGf2128 p.1.maskTriple p.1.mulTriples p.1.mulChallenge = true ∧
      p.1.deltaScalar = 0#256 ∧
      p.2 = zkCommit s₀.secret := by
  induction hTrace with
  | nil _ =>
    intro _ hp; cases hp
  | @accept st st' _ inp out rest hStep _ ih =>
    intro p hp
    dsimp only [idealZeroFaultMachine] at hStep
    cases hAll : (isUniformLaneWord inp.laneMask &&
        evalUpfrontTapeValidity drawValidPred inp.seed0 inp.seed1 inp.seed2 &&
        verifyAllPendingGf2128 inp.maskTriple inp.mulTriples inp.mulChallenge &&
        (inp.deltaScalar == 0#256))
    · rw [hAll] at hStep
      cases hStep
    · rw [hAll] at hStep
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hStep
      rcases hStep with ⟨rfl, rfl⟩
      rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hAll
      rcases List.mem_cons.mp hp with rfl | hMemRest
      · exact ⟨hAll.1.1.1, hAll.1.1.2, hAll.1.2, eq_of_beq hAll.2, rfl⟩
      · exact ih p hMemRest
  | reject _ _ _ ih =>
    intro p hp
    exact ih p hp

/-- Trace invariant and completeness for the ideal scalar-residue machine.
    The separately supplied triples do not affect that ideal computation; this
    theorem must not be used as active gate-execution safety. -/
theorem multi_turn_hardened_ceremony_trace_safe
    {ZkView : Type}
    (group : ScalarGroup)
    (drawValidPred : MigrationKey256 → Bool)
    (zkCommit : MigrationKey256 → ZkView)
    (ks : RssKeyShares3) (hCanon : requireCanonicalScalar group ks.secret = true)
    (comp₀ abort₀ : Nat)
    {st_final : ConcreteCustodianState} {trace : List (RssCeremonyTurnInput × ZkView)}
    (hTrace : (concreteCustodianMachine drawValidPred zkCommit).ValidTrace
      ⟨group, ks, comp₀, abort₀⟩ trace st_final) :
    (∀ p ∈ trace,
      isUniformLaneWord p.1.laneMask = true ∧
      evalUpfrontTapeValidity drawValidPred p.1.seed0 p.1.seed1 p.1.seed2 = true ∧
      verifyAllPendingGf2128 p.1.maskTriple p.1.mulTriples p.1.mulChallenge = true ∧
      p.1.deltaScalar = 0#256 ∧
      p.2 = zkCommit ks.secret) ∧
    (∀ (seed0 seed1 seed2 : MigrationKey256) (chi : Tower128),
      evalUpfrontTapeValidity drawValidPred seed0 seed1 seed2 = true →
      let honestZero : Gf2128MulTriple := ⟨towerZero 7, towerZero 7, towerZero 7⟩
      let honestInp : RssCeremonyTurnInput :=
        { deltaScalar := 0#256
          laneMask := 0
          seed0 := seed0
          seed1 := seed1
          seed2 := seed2
          maskTriple := honestZero
          mulTriples := [honestZero]
          mulChallenge := chi }
      (concreteCustodianMachine drawValidPred zkCommit).step
        ⟨group, ks, comp₀, abort₀⟩ honestInp =
        some (⟨group, ks, comp₀ + 1, abort₀⟩, zkCommit ks.secret)) := by
  let spine := custodian_to_ideal_spine drawValidPred zkCommit
  have hRel₀ : spine.Rel ⟨group, ks, comp₀, abort₀⟩ ⟨group, ks.secret, comp₀, abort₀⟩ := by
    simp only [spine, custodian_to_ideal_spine, ForwardSim.trans_rel, LockstepSim.toForwardSim_rel]
    exact ⟨⟨group, ks.secret, comp₀, abort₀⟩, ⟨trivial, rfl⟩, ⟨rfl, hCanon⟩⟩
  have hSafe := spine.preserve_trace_pred hRel₀
    (fun hIdeal => idealZeroFault_trace_inv drawValidPred zkCommit hIdeal)
    hTrace
  refine ⟨hSafe, ?_⟩
  intro seed0 seed1 seed2 chi hTapeValid honestZero honestInp
  dsimp only [concreteCustodianMachine, honestInp]
  have hUnif0 : isUniformLaneWord 0 = true := by decide
  have hMulOk : verifyAllPendingGf2128 honestZero [honestZero] chi = true := by
    apply verifyAllPendingGf2128_honest_complete
    · dsimp [honestZero]; rw [towerMul_zero]
    · intro t ht
      rcases List.mem_singleton.mp ht with rfl
      dsimp [honestZero]; rw [towerMul_zero]
  have hCandEq : ((ks.s0 ^^^ 0#256) ^^^ ks.s1) ^^^ ks.s2 = ks.secret := by
    unfold RssKeyShares3.secret; bv_xor_cancel
  have hZeroOk : circuitAllOutputsZero group
      (scalarMulKey (canonicalSubgroupHom group) ks.secret)
      (((ks.s0 ^^^ 0#256) ^^^ ks.s1) ^^^ ks.s2) = true :=
    (circuitAllOutputsZero_iff_zero_fault group ks hCanon 0#256).mpr rfl
  rw [hUnif0, hTapeValid, hMulOk, hZeroOk, hCandEq]
  rfl

/-! ## 8. Concrete 256-Bit Inhabitedness Witnesses (`Secp256k1`, `Ed25519`, `Tower128`) -/

/-- Concrete 256-bit inhabitedness witness on canonical `Secp256k1` & `Ed25519` spending scalars
    confirming non-vacuity of canonical range guards, Taproot parity, Ed25519 clamping, and
    the `256`-query premature-open key-recovery `#tooth`! -/
theorem inhabited_migration_256_zero_test_and_tooth :
    let ksSecp : RssKeyShares3 :=
      { s0 := BitVec.ofNat 256 0xdeadbeefcafebabe
        s1 := BitVec.ofNat 256 0x0123456789abcdef
        s2 := BitVec.ofNat 256 0x1122334455667788 }
    let rawEdSeed : MigrationKey256 := BitVec.ofNat 256 0xabcdef0123456789
    let edCanon := normalizeSlip0010Ed25519Scalar rawEdSeed
    let ksEd : RssKeyShares3 := ⟨0#256, edCanon, 0#256⟩
    let delta : MigrationKey256 := oneBitMask 256 137
    let GSecp := canonicalSubgroupHom .Secp256k1
    let pkSecp := scalarMulKey GSecp ksSecp.secret
    requireCanonicalScalar .Secp256k1 ksSecp.secret = true ∧
    requireCanonicalScalar .Ed25519 ksEd.secret = true ∧
    delta ≠ 0#256 ∧
    circuitAllOutputsZero .Secp256k1 pkSecp (((ksSecp.s0 ^^^ delta) ^^^ ksSecp.s1) ^^^ ksSecp.s2) = false ∧
    recoverKeyFromPrematureOpens GSecp pkSecp
      (fun i => (brokenPrematureOpenCeremony (scalarMulKey GSecp) GSecp.encodePk id pkSecp
        ksSecp.s0 ksSecp.s1 ksSecp.s2 (oneBitMask 256 i)).1) = ksSecp.secret := by
  intro ksSecp rawEdSeed edCanon ksEd delta GSecp pkSecp
  have hSecpCanon : requireCanonicalScalar .Secp256k1 ksSecp.secret = true := by
    unfold requireCanonicalScalar ScalarGroup.orderNat SECP256K1_ORDER_N RssKeyShares3.secret
    dsimp [ksSecp]
    decide
  have hEdSecEq : ksEd.secret = edCanon := by dsimp [ksEd, RssKeyShares3.secret]; bv_xor_cancel
  have hEdCanon : requireCanonicalScalar .Ed25519 ksEd.secret = true := by
    rw [hEdSecEq]
    exact slip0010_ed25519_clamped_canonical_nonzero rawEdSeed
  have hDeltaNe : delta ≠ 0#256 := by
    intro hZero
    have hBit : delta.getLsbD 137 = (0#256).getLsbD 137 := congrArg (·.getLsbD 137) hZero
    change (oneBitMask 256 137).getLsbD 137 = (0#256).getLsbD 137 at hBit
    rw [oneBitMask_getLsbD 256 137 137 (by omega), BitVec.getLsbD_zero] at hBit
    cases hBit
  have hZeroTestFalse :
      circuitAllOutputsZero .Secp256k1 pkSecp (((ksSecp.s0 ^^^ delta) ^^^ ksSecp.s1) ^^^ ksSecp.s2) = false := by
    cases h : circuitAllOutputsZero .Secp256k1 pkSecp (((ksSecp.s0 ^^^ delta) ^^^ ksSecp.s1) ^^^ ksSecp.s2)
    · rfl
    · exfalso
      exact hDeltaNe ((circuitAllOutputsZero_iff_zero_fault .Secp256k1 ksSecp hSecpCanon delta).mp h)
  obtain ⟨_, hRecEq, hSecEq, _⟩ :=
    tooth_premature_residual_open_recovers_spending_key GSecp id ksSecp.s0 ksSecp.s1 ksSecp.s2
  exact ⟨hSecpCanon, hEdCanon, hDeltaNe, hZeroTestFalse, hRecEq.symm.trans hSecEq⟩

/-- Concrete inhabitedness witness for `Tower128` BBCGGI19 + coin-permuted triple bucketing at `N = 2`. -/
theorem inhabited_coin_permuted_bucketing_witness :
    let partnerMap : Fin 3 → Fin 4 := fun c => ⟨c.val + 1, by omega⟩
    let chi : Tower128 := towerOne 7
    let deltaL : Tower128 := towerX 7
    let deltaR : Tower128 := towerOne 7
    chi ≠ towerZero 7 ∧
    deltaL ≠ towerZero 7 ∧
    deltaR ≠ towerZero 7 ∧
    Function.Injective partnerMap ∧
    ratLe (1, 4 * (2 * 2 - 1)) (1, 12) := by
  intro partnerMap chi deltaL deltaR
  have hChi : chi ≠ towerZero 7 := towerOne_ne_zero 7
  have hDL : deltaL ≠ towerZero 7 := by
    intro hEq
    have ht := congrArg (towerTrace 7) hEq
    rw [towerTrace_X, towerTrace_zero] at ht
    cases ht
  refine ⟨hChi, hDL, hChi, ?_, ⟨by omega, by omega, by omega⟩⟩
  intro a b hEq
  have hv : a.val + 1 = b.val + 1 := congrArg Fin.val hEq
  exact Fin.ext (by omega)

/-! ## Executable refinement boundaries and persistent settlement -/

namespace MigrationExecution

/-- Rust's little-endian polynomial coefficients, not `packTower 7`. -/
abbrev RustGf128 := BitVec 128

/-- Multiplication by x modulo x^128 + x^7 + x^2 + x + 1. -/
def rustGf128MulX (a : RustGf128) : RustGf128 :=
  (a <<< 1) ^^^ (if a.getLsbD 127 then 0x87#128 else 0#128)

/-- The 128 iterations of `qsag_asm::gf2_128_mul_portable`, with its accumulator
    explicit. The branch denotes Rust's all-zero/all-one selection mask. -/
def rustGf128MulLoop : Nat → RustGf128 → RustGf128 → RustGf128 → RustGf128
  | 0, _, _, acc => acc
  | n + 1, x, y, acc =>
    rustGf128MulLoop n (rustGf128MulX x) (y >>> 1)
      (acc ^^^ (if y.getLsbD 0 then x else 0#128))

def rustGf128Mul (a b : RustGf128) : RustGf128 :=
  rustGf128MulLoop 128 a b 0#128

/-- `[low, high]` in Rust has exactly this coefficient order. -/
def rustGf128OfLimbs (lo hi : UInt64) : RustGf128 :=
  BitVec.ofNat 128 (lo.toNat + 2^64 * hi.toNat)

set_option maxRecDepth 4096 in
theorem rust_gf128_basis_kats :
    rustGf128Mul 2#128 2#128 = 4#128 ∧
    rustGf128Mul (BitVec.ofNat 128 (2^127)) 2#128 = 0x87#128 ∧
    rustGf128OfLimbs 0 1 = BitVec.ofNat 128 (2^64) := by
  decide

/-- Transparent Wiedemann coordinate bit-packing (`TowerElem k ≃ BitVec (2^k)`) free of `BitVec.cast`. -/
def wiedemannToNat : (k : Nat) → TowerElem k → Nat
  | 0, a => match a with | true => 1 | false => 0
  | k + 1, a => wiedemannToNat k a.1 + ((wiedemannToNat k a.2) <<< (2 ^ k))

def wiedemannOfNat : (k : Nat) → Nat → TowerElem k
  | 0, n => n.testBit 0
  | k + 1, n => (wiedemannOfNat k (n % (2 ^ (2 ^ k))), wiedemannOfNat k (n >>> (2 ^ k)))

def wiedemannPack128 (a : Tower128) : BitVec 128 :=
  BitVec.ofNat 128 (wiedemannToNat 7 a)

def wiedemannUnpack128 (v : BitVec 128) : Tower128 :=
  wiedemannOfNat 7 v.toNat

/-- Fast 3-way Karatsuba evaluator for `TowerElem k`, proved equal to `towerMul k`. -/
def wiedemannKaratsuba : (k : Nat) → TowerElem k → TowerElem k → TowerElem k
  | 0, a, b => a && b
  | k + 1, a, b =>
    let p := wiedemannKaratsuba k a.1 b.1
    let q := wiedemannKaratsuba k a.2 b.2
    let r := wiedemannKaratsuba k (towerAdd k a.1 a.2) (towerAdd k b.1 b.2)
    (towerAdd k p q, towerAdd k (towerAdd k r (towerAdd k p q)) (towerScaleX k q))

theorem wiedemannKaratsuba_eq_towerMul (k : Nat) (a b : TowerElem k) :
    wiedemannKaratsuba k a b = towerMul k a b := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [wiedemannKaratsuba, ih, towerMul, towerMul_add_distrib,
      towerAdd_mul_distrib, towerScaleX_eq_mul]
    congr 1
    simp only [towerAdd_assoc, towerAdd_comm, towerAdd_left_comm,
      towerAdd_self_zero, towerAdd_zero, towerAdd_cancel]

/-- Regression against treating Wiedemann coordinate bit-packing as the Rust polynomial basis
    (the verified conversion is `rustToTower` below):
    under naive coordinate bit-packing, bit `1` (`x_0 ∈ Tower128`) squares to `x_0 + 1` (`3#128`),
    whereas in `RustGf128` bit `1` (`x`) squares to `x^2` (`4#128`). -/
theorem tooth_identity_basis_conversion_wrong :
    ∃ x : RustGf128,
      rustGf128Mul x x ≠
        wiedemannPack128 (towerMul 7 (wiedemannUnpack128 x) (wiedemannUnpack128 x)) ∧
      wiedemannUnpack128 (rustGf128Mul x x) ≠
        towerMul 7 (wiedemannUnpack128 x) (wiedemannUnpack128 x) := by
  refine ⟨2#128, ?_⟩
  have hK : towerMul 7 (wiedemannUnpack128 2#128) (wiedemannUnpack128 2#128) =
      wiedemannKaratsuba 7 (wiedemannUnpack128 2#128) (wiedemannUnpack128 2#128) :=
    (wiedemannKaratsuba_eq_towerMul 7 _ _).symm
  have hW : wiedemannPack128 (wiedemannKaratsuba 7 (wiedemannUnpack128 2#128) (wiedemannUnpack128 2#128)) = 3#128 := by
    decide
  have hR : rustGf128Mul 2#128 2#128 = 4#128 := rust_gf128_basis_kats.1
  rw [hK]
  refine ⟨?_, ?_⟩
  · rw [hR, hW]; decide
  · intro hEq
    have hp := congrArg wiedemannPack128 hEq
    rw [hW] at hp
    have h4 : wiedemannPack128 (wiedemannUnpack128 (rustGf128Mul 2#128 2#128)) = 4#128 := by
      rw [hR]; decide
    rw [h4] at hp
    revert hp; decide

#tooth_pair Qsag.MigrationExecution.rust_gf128_basis_kats vs
  Qsag.MigrationExecution.tooth_identity_basis_conversion_wrong

/-! ### The Rust polynomial basis is a field isomorphic to `Tower128`

Ring laws are proved directly on the shift-and-reduce loop: multiplication by
`b` is the polynomial `b` evaluated at the linear operator `rustGf128MulX`, and
polynomials in one operator commute. The seven Wiedemann generators are then
located inside the Rust basis, which gives a ring homomorphism out of the tower
field; its inverse is Horner evaluation at a root of
`x^128 + x^7 + x^2 + x + 1` in the tower. -/

/-- `Σ_{i<n, f i} X^i · x`: the bits `f` of one multiplicand act on the other. -/
def rustPolyAct : Nat → (Nat → Bool) → RustGf128 → RustGf128
  | 0, _, _ => 0#128
  | n + 1, f, x =>
    (if f 0 then x else 0#128) ^^^ rustPolyAct n (fun i => f (i + 1)) (rustGf128MulX x)

private theorem bxor_left_comm (a b c : RustGf128) : a ^^^ (b ^^^ c) = b ^^^ (a ^^^ c) := by
  rw [← BitVec.xor_assoc, BitVec.xor_comm a b, BitVec.xor_assoc]

private theorem bxor_cancel (a b : RustGf128) : a ^^^ (a ^^^ b) = b := by
  rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

theorem rustGf128MulLoop_eq (n : Nat) : ∀ (x y acc : RustGf128),
    rustGf128MulLoop n x y acc = acc ^^^ rustPolyAct n y.getLsbD x := by
  induction n with
  | zero =>
    intro x y acc
    show acc = acc ^^^ 0#128
    rw [BitVec.xor_zero]
  | succ n ih =>
    intro x y acc
    have hShift : (y >>> 1).getLsbD = fun i => y.getLsbD (i + 1) := by
      funext i
      rw [BitVec.getLsbD_ushiftRight, Nat.add_comm]
    show rustGf128MulLoop n (rustGf128MulX x) (y >>> 1)
        (acc ^^^ (if y.getLsbD 0 then x else 0#128)) =
      acc ^^^ ((if y.getLsbD 0 then x else 0#128) ^^^
        rustPolyAct n (fun i => y.getLsbD (i + 1)) (rustGf128MulX x))
    rw [ih, hShift, BitVec.xor_assoc]

theorem rustGf128Mul_eq_act (a b : RustGf128) :
    rustGf128Mul a b = rustPolyAct 128 b.getLsbD a := by
  unfold rustGf128Mul
  rw [rustGf128MulLoop_eq, BitVec.zero_xor]

private theorem rustGf128MulX_zero : rustGf128MulX 0#128 = 0#128 := by decide

private theorem ite_xor_split (c d : Bool) (k p q : RustGf128) :
    (p ^^^ q) ^^^ (if (c ^^ d) = true then k else 0#128) =
      (p ^^^ (if c = true then k else 0#128)) ^^^ (q ^^^ (if d = true then k else 0#128)) := by
  cases c <;> cases d
  · show (p ^^^ q) ^^^ 0#128 = (p ^^^ 0#128) ^^^ (q ^^^ 0#128)
    simp only [BitVec.xor_zero]
  · show (p ^^^ q) ^^^ k = (p ^^^ 0#128) ^^^ (q ^^^ k)
    simp only [BitVec.xor_zero, BitVec.xor_assoc]
  · show (p ^^^ q) ^^^ k = (p ^^^ k) ^^^ (q ^^^ 0#128)
    simp only [BitVec.xor_zero, BitVec.xor_comm, bxor_left_comm]
  · show (p ^^^ q) ^^^ 0#128 = (p ^^^ k) ^^^ (q ^^^ k)
    simp only [BitVec.xor_zero, BitVec.xor_assoc, BitVec.xor_comm, bxor_left_comm, bxor_cancel]

private theorem rustGf128MulX_xor (a b : RustGf128) :
    rustGf128MulX (a ^^^ b) = rustGf128MulX a ^^^ rustGf128MulX b := by
  unfold rustGf128MulX
  rw [BitVec.shiftLeft_xor_distrib, BitVec.getLsbD_xor]
  exact ite_xor_split _ _ _ _ _

private theorem rustGf128MulX_ite (c : Bool) (x : RustGf128) :
    rustGf128MulX (if c then x else 0#128) = if c then rustGf128MulX x else 0#128 := by
  cases c
  · exact rustGf128MulX_zero
  · rfl

theorem rustPolyAct_zero (n : Nat) : ∀ f, rustPolyAct n f 0#128 = 0#128 := by
  induction n with
  | zero => intro f; rfl
  | succ n ih =>
    intro f
    simp only [rustPolyAct]
    rw [rustGf128MulX_zero, ih]
    cases f 0 <;> decide

theorem rustPolyAct_xor (n : Nat) : ∀ f x y,
    rustPolyAct n f (x ^^^ y) = rustPolyAct n f x ^^^ rustPolyAct n f y := by
  induction n with
  | zero => intro f x y; simp only [rustPolyAct, BitVec.xor_zero]
  | succ n ih =>
    intro f x y
    simp only [rustPolyAct]
    rw [rustGf128MulX_xor, ih]
    generalize rustPolyAct n (fun i => f (i + 1)) (rustGf128MulX x) = P
    generalize rustPolyAct n (fun i => f (i + 1)) (rustGf128MulX y) = Q
    cases f 0
    · show 0#128 ^^^ (P ^^^ Q) = (0#128 ^^^ P) ^^^ (0#128 ^^^ Q)
      simp only [BitVec.zero_xor]
    · show (x ^^^ y) ^^^ (P ^^^ Q) = (x ^^^ P) ^^^ (y ^^^ Q)
      simp only [BitVec.xor_assoc, bxor_left_comm]

private theorem rustPolyAct_ite (n : Nat) (f : Nat → Bool) (c : Bool) (x : RustGf128) :
    rustPolyAct n f (if c then x else 0#128) = if c then rustPolyAct n f x else 0#128 := by
  cases c
  · exact rustPolyAct_zero n f
  · rfl

theorem rustPolyAct_mulX (n : Nat) : ∀ f x,
    rustPolyAct n f (rustGf128MulX x) = rustGf128MulX (rustPolyAct n f x) := by
  induction n with
  | zero => intro f x; exact rustGf128MulX_zero.symm
  | succ n ih =>
    intro f x
    simp only [rustPolyAct]
    rw [rustGf128MulX_xor, rustGf128MulX_ite, ih (fun i => f (i + 1)) (rustGf128MulX x)]

/-- Polynomials in the single operator `rustGf128MulX` commute. -/
theorem rustPolyAct_comm (n m : Nat) (h : Nat → Bool) : ∀ f x,
    rustPolyAct n f (rustPolyAct m h x) = rustPolyAct m h (rustPolyAct n f x) := by
  induction n with
  | zero => intro f x; exact (rustPolyAct_zero m h).symm
  | succ n ih =>
    intro f x
    simp only [rustPolyAct]
    rw [rustPolyAct_xor, rustPolyAct_ite, ← rustPolyAct_mulX m h x,
      ih (fun i => f (i + 1)) (rustGf128MulX x)]

private theorem twoPow_bit (j i : Nat) (hj : j < 128) :
    (BitVec.twoPow 128 j).getLsbD i = decide (j = i) := by
  rw [BitVec.getLsbD_twoPow, decide_eq_true hj]
  rfl

private theorem ite_twoPow_bit (c : Bool) (j i : Nat) (hj : j < 128) :
    (if c then BitVec.twoPow 128 j else 0#128).getLsbD i = (c && decide (j = i)) := by
  cases c
  · exact BitVec.getLsbD_zero
  · exact twoPow_bit j i hj

private theorem rustGf128MulX_twoPow (j : Nat) (hj : j < 127) :
    rustGf128MulX (BitVec.twoPow 128 j) = BitVec.twoPow 128 (j + 1) := by
  unfold rustGf128MulX
  rw [twoPow_bit j 127 (by omega), decide_eq_false (by omega : ¬ j = 127)]
  show (1#128 <<< j) <<< 1 ^^^ 0#128 = 1#128 <<< (j + 1)
  rw [BitVec.xor_zero, BitVec.shiftLeft_add]

/-- No reduction happens below degree 128: the action on `X^j` writes the bits
    of `f` at positions `j, …, j+n-1`. -/
theorem rustPolyAct_twoPow_bit (n : Nat) : ∀ (j : Nat) (f : Nat → Bool), j + n ≤ 128 → ∀ i,
    (rustPolyAct n f (BitVec.twoPow 128 j)).getLsbD i =
      (decide (j ≤ i) && decide (i < j + n) && f (i - j)) := by
  induction n with
  | zero =>
    intro j f _ i
    show (0#128).getLsbD i = _
    rw [BitVec.getLsbD_zero]
    by_cases h : j ≤ i
    · rw [decide_eq_false (by omega : ¬ i < j + 0)]
      simp only [Bool.and_false, Bool.false_and]
    · rw [decide_eq_false h]
      rfl
  | succ n ih =>
    intro j f hjn i
    have hj : j < 128 := by omega
    simp only [rustPolyAct]
    rw [BitVec.getLsbD_xor, ite_twoPow_bit _ j i hj]
    have hRest : (rustPolyAct n (fun i => f (i + 1))
          (rustGf128MulX (BitVec.twoPow 128 j))).getLsbD i =
        (decide (j + 1 ≤ i) && decide (i < j + (n + 1)) && f (i - (j + 1) + 1)) := by
      by_cases hn : n = 0
      · subst hn
        show (0#128).getLsbD i = _
        rw [BitVec.getLsbD_zero]
        by_cases h : j + 1 ≤ i
        · rw [decide_eq_false (by omega : ¬ i < j + (0 + 1))]
          simp only [Bool.and_false, Bool.false_and]
        · rw [decide_eq_false h]
          rfl
      · rw [rustGf128MulX_twoPow j (by omega), ih (j + 1) _ (by omega) i,
          show j + 1 + n = j + (n + 1) from by omega]
    rw [hRest]
    rcases Nat.lt_trichotomy i j with h | h | h
    · rw [decide_eq_false (by omega : ¬ j = i), decide_eq_false (by omega : ¬ j + 1 ≤ i),
        decide_eq_false (by omega : ¬ j ≤ i)]
      cases f 0 <;> rfl
    · subst h
      rw [decide_eq_true (Eq.refl i), decide_eq_false (by omega : ¬ i + 1 ≤ i),
        decide_eq_true (Nat.le_refl i), decide_eq_true (by omega : i < i + (n + 1)),
        Nat.sub_self]
      cases f 0 <;> rfl
    · rw [decide_eq_false (by omega : ¬ j = i), decide_eq_true (by omega : j + 1 ≤ i),
        decide_eq_true (by omega : j ≤ i), show i - (j + 1) + 1 = i - j from by omega]
      cases f 0 <;> cases decide (i < j + (n + 1)) <;> cases f (i - j) <;> rfl

/-- Every element is its own bit polynomial applied to `1`. -/
theorem rustPolyAct_bits_one (a : RustGf128) : rustPolyAct 128 a.getLsbD 1#128 = a := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h := rustPolyAct_twoPow_bit 128 0 a.getLsbD (by omega) i
  rw [show BitVec.twoPow 128 0 = 1#128 from by decide] at h
  rw [h, decide_eq_true (Nat.zero_le i), decide_eq_true (by omega : i < 0 + 128), Nat.sub_zero]
  rfl

theorem rustGf128Mul_comm (a b : RustGf128) : rustGf128Mul a b = rustGf128Mul b a := by
  rw [rustGf128Mul_eq_act, rustGf128Mul_eq_act]
  calc rustPolyAct 128 b.getLsbD a
      = rustPolyAct 128 b.getLsbD (rustPolyAct 128 a.getLsbD 1#128) := by
        rw [rustPolyAct_bits_one]
    _ = rustPolyAct 128 a.getLsbD (rustPolyAct 128 b.getLsbD 1#128) :=
        rustPolyAct_comm 128 128 a.getLsbD b.getLsbD 1#128
    _ = rustPolyAct 128 a.getLsbD b := by rw [rustPolyAct_bits_one]

theorem rustGf128Mul_xor_left (a b c : RustGf128) :
    rustGf128Mul (a ^^^ b) c = rustGf128Mul a c ^^^ rustGf128Mul b c := by
  simp only [rustGf128Mul_eq_act, rustPolyAct_xor]

theorem rustGf128Mul_xor_right (a b c : RustGf128) :
    rustGf128Mul a (b ^^^ c) = rustGf128Mul a b ^^^ rustGf128Mul a c := by
  rw [rustGf128Mul_comm a, rustGf128Mul_xor_left, rustGf128Mul_comm b a, rustGf128Mul_comm c a]

theorem rustGf128Mul_assoc (a b c : RustGf128) :
    rustGf128Mul (rustGf128Mul a b) c = rustGf128Mul a (rustGf128Mul b c) := by
  rw [rustGf128Mul_comm a (rustGf128Mul b c), rustGf128Mul_comm a b]
  simp only [rustGf128Mul_eq_act]
  exact rustPolyAct_comm 128 128 a.getLsbD c.getLsbD b

theorem rustGf128Mul_left_comm (a b c : RustGf128) :
    rustGf128Mul a (rustGf128Mul b c) = rustGf128Mul b (rustGf128Mul a c) := by
  rw [← rustGf128Mul_assoc, rustGf128Mul_comm a b, rustGf128Mul_assoc]

theorem rustGf128Mul_one_left (a : RustGf128) : rustGf128Mul 1#128 a = a := by
  rw [rustGf128Mul_eq_act, rustPolyAct_bits_one]

theorem rustGf128Mul_one_right (a : RustGf128) : rustGf128Mul a 1#128 = a := by
  rw [rustGf128Mul_comm, rustGf128Mul_one_left]

theorem rustGf128Mul_zero_left (a : RustGf128) : rustGf128Mul 0#128 a = 0#128 := by
  rw [rustGf128Mul_eq_act, rustPolyAct_zero]

theorem rustGf128Mul_zero_right (a : RustGf128) : rustGf128Mul a 0#128 = 0#128 := by
  rw [rustGf128Mul_comm, rustGf128Mul_zero_left]

theorem rustGf128MulX_eq_mul (a : RustGf128) : rustGf128MulX a = rustGf128Mul 2#128 a := by
  rw [rustGf128Mul_eq_act, show (2#128 : RustGf128) = rustGf128MulX 1#128 from by decide,
    rustPolyAct_mulX, rustPolyAct_bits_one]

/-- The Rust polynomial basis as a commutative ring: addition is XOR and
    multiplication is the shift-and-reduce loop. Scoped so that no other
    `BitVec 128` carrier silently inherits this multiplication. -/
scoped instance rustGf128Ring : LawfulCommRing RustGf128 where
  zero := 0#128
  one := 1#128
  add a b := a ^^^ b
  mul := rustGf128Mul
  neg a := a
  sub a b := a ^^^ b
  add_assoc := BitVec.xor_assoc
  add_comm := BitVec.xor_comm
  zero_add _ := BitVec.zero_xor
  add_zero _ := BitVec.xor_zero
  add_left_neg _ := BitVec.xor_self
  sub_eq_add_neg _ _ := rfl
  mul_assoc := rustGf128Mul_assoc
  mul_comm := rustGf128Mul_comm
  one_mul := rustGf128Mul_one_left
  mul_one := rustGf128Mul_one_right
  left_distrib := rustGf128Mul_xor_right
  right_distrib := rustGf128Mul_xor_left

/-- Images of the Wiedemann generators `t_k` (`t_0 = 1`,
    `t_{k+1}^2 = t_{k+1} t_k + 1`) in the Rust basis. -/
def towerGenRust : Nat → RustGf128
  | 0 => 1#128
  | 1 => 0x295ac0b1f4731af9676aac9fa4b20b08#128
  | 2 => 0x500317bd159d73bb34d2f7fba603e341#128
  | 3 => 0xd7272761ca8e287777eda49fad5950db#128
  | 4 => 0xf7ee5366ad8dcdf077be5724c64eb1d2#128
  | 5 => 0x218cc1384d3fe56b1428b68814f535be#128
  | 6 => 0x2c2fcdaa2679817f994e36d0d1df3b3d#128
  | 7 => 0xe4f21e8c8ec8031cb7b73094152f7631#128
  | _ => 0#128

theorem towerGenRust_sq (k : Nat) (hk : k < 7) :
    rustGf128Mul (towerGenRust (k + 1)) (towerGenRust (k + 1)) =
      rustGf128Mul (towerGenRust (k + 1)) (towerGenRust k) ^^^ 1#128 := by
  have h : ∀ k : Fin 7,
      rustGf128Mul (towerGenRust (k.val + 1)) (towerGenRust (k.val + 1)) =
        rustGf128Mul (towerGenRust (k.val + 1)) (towerGenRust k.val) ^^^ 1#128 := by
    decide +kernel
  exact h ⟨k, hk⟩

/-- The tower embedded in the Rust basis, one quadratic extension at a time. -/
def towerToRust : (k : Nat) → TowerElem k → RustGf128
  | 0, a => match a with | true => 1#128 | false => 0#128
  | k + 1, a =>
    towerToRust k a.1 ^^^ rustGf128Mul (towerToRust k a.2) (towerGenRust (k + 1))

theorem towerToRust_zero (k : Nat) : towerToRust k (towerZero k) = 0#128 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show towerToRust k (towerZero k) ^^^
      rustGf128Mul (towerToRust k (towerZero k)) (towerGenRust (k + 1)) = 0#128
    rw [ih, rustGf128Mul_zero_left, BitVec.xor_zero]

theorem towerToRust_one (k : Nat) : towerToRust k (towerOne k) = 1#128 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show towerToRust k (towerOne k) ^^^
      rustGf128Mul (towerToRust k (towerZero k)) (towerGenRust (k + 1)) = 1#128
    rw [ih, towerToRust_zero, rustGf128Mul_zero_left, BitVec.xor_zero]

theorem towerToRust_add (k : Nat) (a b : TowerElem k) :
    towerToRust k (towerAdd k a b) = towerToRust k a ^^^ towerToRust k b := by
  induction k with
  | zero => cases a <;> cases b <;> decide
  | succ k ih =>
    show towerToRust k (towerAdd k a.1 b.1) ^^^
        rustGf128Mul (towerToRust k (towerAdd k a.2 b.2)) (towerGenRust (k + 1)) =
      (towerToRust k a.1 ^^^ rustGf128Mul (towerToRust k a.2) (towerGenRust (k + 1))) ^^^
      (towerToRust k b.1 ^^^ rustGf128Mul (towerToRust k b.2) (towerGenRust (k + 1)))
    rw [ih, ih, rustGf128Mul_xor_left]
    simp only [BitVec.xor_assoc, bxor_left_comm]

theorem towerToRust_X (k : Nat) : towerToRust k (towerX k) = towerGenRust k := by
  cases k with
  | zero => rfl
  | succ k =>
    show towerToRust k (towerZero k) ^^^
      rustGf128Mul (towerToRust k (towerOne k)) (towerGenRust (k + 1)) = towerGenRust (k + 1)
    rw [towerToRust_zero, towerToRust_one, rustGf128Mul_one_left, BitVec.zero_xor]

set_option linter.unusedSimpArgs false in
private theorem rust_tower_step (A1 A2 B1 B2 T U : RustGf128)
    (hT : rustGf128Mul T T = rustGf128Mul T U ^^^ 1#128) :
    (rustGf128Mul A1 B1 ^^^ rustGf128Mul A2 B2) ^^^
      rustGf128Mul ((rustGf128Mul A1 B2 ^^^ rustGf128Mul A2 B1) ^^^
        rustGf128Mul U (rustGf128Mul A2 B2)) T =
    rustGf128Mul (A1 ^^^ rustGf128Mul A2 T) (B1 ^^^ rustGf128Mul B2 T) := by
  have hs : rustGf128Mul (rustGf128Mul A2 T) (rustGf128Mul B2 T) =
      rustGf128Mul (rustGf128Mul A2 B2) (rustGf128Mul T T) := by
    simp only [rustGf128Mul_comm, rustGf128Mul_left_comm]
  have h4 : rustGf128Mul (rustGf128Mul A2 T) (rustGf128Mul B2 T) =
      rustGf128Mul (rustGf128Mul A2 B2) (rustGf128Mul T U) ^^^ rustGf128Mul A2 B2 := by
    rw [hs, hT, rustGf128Mul_xor_right, rustGf128Mul_one_right]
  rw [rustGf128Mul_xor_left A1 (rustGf128Mul A2 T), rustGf128Mul_xor_right A1,
    rustGf128Mul_xor_right (rustGf128Mul A2 T), h4]
  simp only [rustGf128Mul_xor_right, rustGf128Mul_comm,
    rustGf128Mul_left_comm, BitVec.xor_assoc, BitVec.xor_comm, bxor_left_comm]

theorem towerToRust_mul : ∀ (k : Nat), k ≤ 7 → ∀ a b : TowerElem k,
    towerToRust k (towerMul k a b) =
      rustGf128Mul (towerToRust k a) (towerToRust k b) := by
  intro k
  induction k with
  | zero => intro _ a b; cases a <;> cases b <;> decide +kernel
  | succ k ih =>
    intro hk a b
    have ih' := ih (by omega)
    show towerToRust k (towerAdd k (towerMul k a.1 b.1) (towerMul k a.2 b.2)) ^^^
        rustGf128Mul (towerToRust k (towerAdd k
          (towerAdd k (towerMul k a.1 b.2) (towerMul k a.2 b.1))
          (towerMul k (towerX k) (towerMul k a.2 b.2)))) (towerGenRust (k + 1)) =
      rustGf128Mul (towerToRust k a.1 ^^^ rustGf128Mul (towerToRust k a.2) (towerGenRust (k + 1)))
        (towerToRust k b.1 ^^^ rustGf128Mul (towerToRust k b.2) (towerGenRust (k + 1)))
    simp only [towerToRust_add, ih', towerToRust_X]
    exact rust_tower_step _ _ _ _ _ _ (towerGenRust_sq k (by omega))

/-- A ring homomorphism out of a field is injective. -/
theorem towerToRust_injective (a b : Tower128)
    (h : towerToRust 7 a = towerToRust 7 b) : a = b := by
  have hsum : towerToRust 7 (towerAdd 7 a b) = 0#128 := by
    rw [towerToRust_add, h, BitVec.xor_self]
  by_cases hz : towerAdd 7 a b = towerZero 7
  · have hc := towerAdd_cancel 7 a b
    rw [hz, towerAdd_zero] at hc
    exact hc
  · exfalso
    have h1 := congrArg (towerToRust 7) (towerMul_inv 7 _ hz)
    rw [towerToRust_mul 7 (Nat.le_refl 7), hsum, rustGf128Mul_zero_left, towerToRust_one] at h1
    exact absurd h1 (by decide)

/-- A root of `x^128 + x^7 + x^2 + x + 1` in the Wiedemann tower: the image of
    Rust's `x` (`2#128`). -/
def rustGenTower : Tower128 :=
  wiedemannOfNat 7 0xbfe0a17ee2b77754526b13e1fedaef3d

theorem towerToRust_rustGenTower : towerToRust 7 rustGenTower = 2#128 := by
  decide +kernel

def rustToTowerAux : Nat → (Nat → Bool) → Tower128
  | 0, _ => towerZero 7
  | n + 1, f =>
    towerAdd 7 (if f 0 then towerOne 7 else towerZero 7)
      (towerMul 7 rustGenTower (rustToTowerAux n (fun i => f (i + 1))))

/-- The basis conversion: Horner evaluation of the Rust coefficient bits at
    `rustGenTower`. This, not coordinate repacking, relates the two carriers. -/
def rustToTower (a : RustGf128) : Tower128 := rustToTowerAux 128 a.getLsbD

private theorem towerToRust_bit (c : Bool) :
    towerToRust 7 (if c then towerOne 7 else towerZero 7) = if c then 1#128 else 0#128 := by
  cases c
  · exact towerToRust_zero 7
  · exact towerToRust_one 7

theorem towerToRust_rustToTowerAux (n : Nat) : ∀ f,
    towerToRust 7 (rustToTowerAux n f) = rustPolyAct n f 1#128 := by
  induction n with
  | zero => intro f; exact towerToRust_zero 7
  | succ n ih =>
    intro f
    simp only [rustToTowerAux, rustPolyAct]
    rw [towerToRust_add, towerToRust_mul 7 (Nat.le_refl 7), towerToRust_rustGenTower, ih,
      towerToRust_bit, rustPolyAct_mulX, rustGf128MulX_eq_mul]

theorem towerToRust_rustToTower (a : RustGf128) : towerToRust 7 (rustToTower a) = a := by
  unfold rustToTower
  rw [towerToRust_rustToTowerAux, rustPolyAct_bits_one]

theorem rustToTower_towerToRust (t : Tower128) : rustToTower (towerToRust 7 t) = t :=
  towerToRust_injective _ _ (towerToRust_rustToTower _)

theorem rustToTower_injective (a b : RustGf128) (h : rustToTower a = rustToTower b) : a = b := by
  have hc := congrArg (towerToRust 7) h
  rw [towerToRust_rustToTower, towerToRust_rustToTower] at hc
  exact hc

theorem rustToTower_xor (a b : RustGf128) :
    rustToTower (a ^^^ b) = towerAdd 7 (rustToTower a) (rustToTower b) := by
  apply towerToRust_injective
  rw [towerToRust_rustToTower, towerToRust_add, towerToRust_rustToTower, towerToRust_rustToTower]

/-- The conversion carries Rust's multiplication to tower multiplication for
    every pair of field elements. -/
theorem rustToTower_mul (a b : RustGf128) :
    rustToTower (rustGf128Mul a b) = towerMul 7 (rustToTower a) (rustToTower b) := by
  apply towerToRust_injective
  rw [towerToRust_rustToTower, towerToRust_mul 7 (Nat.le_refl 7), towerToRust_rustToTower,
    towerToRust_rustToTower]

theorem rustToTower_zero : rustToTower 0#128 = towerZero 7 := by
  apply towerToRust_injective
  rw [towerToRust_rustToTower, towerToRust_zero]

theorem rustToTower_two : rustToTower 2#128 = rustGenTower := by
  apply towerToRust_injective
  rw [towerToRust_rustToTower, towerToRust_rustGenTower]

/-- `x^128 + x^7 + x^2 + x + 1` has no proper factorisation: the quotient ring
    Rust computes in has no zero divisors. -/
theorem rustGf128Mul_eq_zero (a b : RustGf128) (h : rustGf128Mul a b = 0#128) :
    a = 0#128 ∨ b = 0#128 := by
  have ht : towerMul 7 (rustToTower a) (rustToTower b) = towerZero 7 := by
    rw [← rustToTower_mul, h, rustToTower_zero]
  rcases (towerMul_eq_zero_iff 7 _ _).mp ht with h1 | h1
  · exact Or.inl (rustToTower_injective _ _ (h1.trans rustToTower_zero.symm))
  · exact Or.inr (rustToTower_injective _ _ (h1.trans rustToTower_zero.symm))

scoped instance rustGf128NoZeroDivisors : NoZeroDivisors RustGf128 where
  eq_zero_or_eq_zero_of_mul_eq_zero h := rustGf128Mul_eq_zero _ _ h

#tooth_pair Qsag.MigrationExecution.rustToTower_mul vs
  Qsag.MigrationExecution.tooth_identity_basis_conversion_wrong

/-- One base-case opening. Gamma is a received claim, never assigned alpha*beta
    by the verifier. All 2 × 64 openings must pass. This is the final base-case
    check only; the recursive folding-to-gates refinement remains separate. -/
structure BaseOpening where
  alpha : RustGf128
  beta : RustGf128
  gamma : RustGf128
  deriving DecidableEq

def BaseOpening.check (o : BaseOpening) : Bool :=
  o.gamma == rustGf128Mul o.alpha o.beta

def checkBaseOpenings (openings : Fin 2 → Fin 64 → BaseOpening) : Bool :=
  finAll 2 (fun t => finAll 64 (fun lane => (openings t lane).check))

theorem checkBaseOpenings_sound (openings : Fin 2 → Fin 64 → BaseOpening)
    (h : checkBaseOpenings openings = true) :
    ∀ t lane, (openings t lane).gamma =
      rustGf128Mul (openings t lane).alpha (openings t lane).beta := by
  intro t lane
  exact eq_of_beq ((finAll_eq_true_iff 64 _).mp
    ((finAll_eq_true_iff 2 _).mp h t) lane)

/-- The base-case polynomial evaluated by Rust from the folded claim and
    reshared d1/d2, including the actual received gamma. No correctness of the
    supplied d1/d2 or randomness of rb is assumed by this definition. -/
def baseOpening (a b c u v d1 d2 rb : RustGf128) : BaseOpening where
  alpha := a ^^^ rustGf128Mul u rb
  beta := b ^^^ rustGf128Mul v rb
  gamma := c ^^^ rustGf128Mul d1 rb ^^^ rustGf128Mul d2 (rustGf128Mul rb rb)

/-! ### Recursive inner-product sacrifice in the Rust basis: fresh-coin soundness

This models `verify_pending_bits_slice` from the inner-product claim onward: the
arity-2 folds (`h0`, `h1` reshared, then the coin `rk`) and the masked base case
(`u`, `v`, `d1`, `d2` fixed, then the coin `rb`). A prover is a strategy tree, so
each message may depend on every earlier coin and on nothing later. The batching
of AND gates into the first inner-product claim, and the PRSS/reshare transport
of these values, are outside this model. -/

/-- `Σ_{i<n} a i · b i`. -/
def rustDot : Nat → (Nat → RustGf128) → (Nat → RustGf128) → RustGf128
  | 0, _, _ => 0#128
  | n + 1, a, b => rustDot n a b ^^^ rustGf128Mul (a n) (b n)

theorem rustDot_congr (n : Nat) (a a' b b' : Nat → RustGf128)
    (ha : ∀ i, i < n → a i = a' i) (hb : ∀ i, i < n → b i = b' i) :
    rustDot n a b = rustDot n a' b' := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show rustDot n a b ^^^ rustGf128Mul (a n) (b n) =
      rustDot n a' b' ^^^ rustGf128Mul (a' n) (b' n)
    rw [ih (fun i hi => ha i (by omega)) (fun i hi => hb i (by omega)),
      ha n (by omega), hb n (by omega)]

theorem rustDot_add (n : Nat) (a b : Nat → RustGf128) : ∀ m,
    rustDot (n + m) a b =
      rustDot n a b ^^^ rustDot m (fun i => a (n + i)) (fun i => b (n + i)) := by
  intro m
  induction m with
  | zero =>
    show rustDot n a b = rustDot n a b ^^^ 0#128
    rw [BitVec.xor_zero]
  | succ m ih =>
    show rustDot (n + m) a b ^^^ rustGf128Mul (a (n + m)) (b (n + m)) =
      rustDot n a b ^^^ (rustDot m (fun i => a (n + i)) (fun i => b (n + i)) ^^^
        rustGf128Mul (a (n + m)) (b (n + m)))
    rw [ih, BitVec.xor_assoc]

/-- Zero padding past the live length, as Rust pushes zero quads on odd counts. -/
def padded (len : Nat) (v : Nat → RustGf128) : Nat → RustGf128 :=
  fun i => if i < len then v i else 0#128

private theorem padded_lt (len : Nat) (v : Nat → RustGf128) (i : Nat) (h : i < len) :
    padded len v i = v i := by
  simp only [padded, h, ↓reduceIte]

private theorem padded_ge (len : Nat) (v : Nat → RustGf128) (i : Nat) (h : len ≤ i) :
    padded len v i = 0#128 := by
  simp only [padded, show ¬ i < len from by omega, ↓reduceIte]

theorem rustDot_padded (len : Nat) (a b : Nat → RustGf128) : ∀ d,
    rustDot (len + d) (padded len a) (padded len b) = rustDot len a b := by
  intro d
  induction d with
  | zero =>
    exact rustDot_congr len _ _ _ _ (fun i hi => padded_lt len a i hi)
      (fun i hi => padded_lt len b i hi)
  | succ d ih =>
    show rustDot (len + d) (padded len a) (padded len b) ^^^
      rustGf128Mul (padded len a (len + d)) (padded len b (len + d)) = _
    rw [ih, padded_ge len a (len + d) (by omega), rustGf128Mul_zero_left, BitVec.xor_zero]

/-- An inner-product claim `⟨a, b⟩ = c` over `len` field elements. -/
structure IpClaim where
  len : Nat
  a : Nat → RustGf128
  b : Nat → RustGf128
  c : RustGf128

/-- The claim's defect; it is zero exactly when the claim is true. -/
def IpClaim.err (s : IpClaim) : RustGf128 := rustDot s.len s.a s.b ^^^ s.c

def IpClaim.half (s : IpClaim) : Nat := (s.len + 1) / 2

def IpClaim.crossLoHi (s : IpClaim) : RustGf128 :=
  rustDot s.half (padded s.len s.a) (fun i => padded s.len s.b (s.half + i))

def IpClaim.crossHiLo (s : IpClaim) : RustGf128 :=
  rustDot s.half (fun i => padded s.len s.a (s.half + i)) (padded s.len s.b)

/-- The two reshared cross terms of one fold round, fixed before its coin. -/
structure FoldMessage where
  h0 : RustGf128
  h1 : RustGf128

/-- One arity-2 fold: `a' = a_lo + rk·a_hi`, `b' = rk·b_lo + b_hi`,
    `c' = h0 + rk·c + rk²·h1`. -/
def foldRound (s : IpClaim) (m : FoldMessage) (rk : RustGf128) : IpClaim where
  len := s.half
  a := fun i => padded s.len s.a i ^^^ rustGf128Mul (padded s.len s.a (s.half + i)) rk
  b := fun i => rustGf128Mul (padded s.len s.b i) rk ^^^ padded s.len s.b (s.half + i)
  c := m.h0 ^^^ rustGf128Mul s.c rk ^^^ rustGf128Mul m.h1 (rustGf128Mul rk rk)

set_option linter.unusedSimpArgs false in
private theorem rustDot_fold (rk : RustGf128) (aLo aHi bLo bHi : Nat → RustGf128) : ∀ n,
    rustDot n (fun i => aLo i ^^^ rustGf128Mul (aHi i) rk)
        (fun i => rustGf128Mul (bLo i) rk ^^^ bHi i) =
      rustDot n aLo bHi ^^^
        rustGf128Mul (rustDot n aLo bLo ^^^ rustDot n aHi bHi) rk ^^^
        rustGf128Mul (rustDot n aHi bLo) (rustGf128Mul rk rk) := by
  intro n
  induction n with
  | zero =>
    show (0#128 : RustGf128) = 0#128 ^^^ rustGf128Mul (0#128 ^^^ 0#128) rk ^^^
      rustGf128Mul 0#128 (rustGf128Mul rk rk)
    simp only [BitVec.xor_zero, rustGf128Mul_zero_left]
  | succ n ih =>
    show rustDot n (fun i => aLo i ^^^ rustGf128Mul (aHi i) rk)
          (fun i => rustGf128Mul (bLo i) rk ^^^ bHi i) ^^^
        rustGf128Mul (aLo n ^^^ rustGf128Mul (aHi n) rk) (rustGf128Mul (bLo n) rk ^^^ bHi n) =
      (rustDot n aLo bHi ^^^ rustGf128Mul (aLo n) (bHi n)) ^^^
        rustGf128Mul ((rustDot n aLo bLo ^^^ rustGf128Mul (aLo n) (bLo n)) ^^^
          (rustDot n aHi bHi ^^^ rustGf128Mul (aHi n) (bHi n))) rk ^^^
        rustGf128Mul (rustDot n aHi bLo ^^^ rustGf128Mul (aHi n) (bLo n)) (rustGf128Mul rk rk)
    rw [ih]
    simp only [rustGf128Mul_xor_left, rustGf128Mul_xor_right, rustGf128Mul_assoc,
      rustGf128Mul_comm, rustGf128Mul_left_comm, BitVec.xor_assoc, BitVec.xor_comm,
      bxor_left_comm]

theorem rustDot_split_half (s : IpClaim) :
    rustDot s.len s.a s.b =
      rustDot s.half (padded s.len s.a) (padded s.len s.b) ^^^
      rustDot s.half (fun i => padded s.len s.a (s.half + i))
        (fun i => padded s.len s.b (s.half + i)) := by
  have hd : s.half + s.half = s.len + (s.half + s.half - s.len) := by
    unfold IpClaim.half
    omega
  rw [← rustDot_add, hd, rustDot_padded]

set_option linter.unusedSimpArgs false in
/-- The folded defect is a quadratic in the coin whose middle coefficient is
    the incoming defect; the outer coefficients are the cross-term errors. -/
theorem foldRound_err (s : IpClaim) (m : FoldMessage) (rk : RustGf128) :
    (foldRound s m rk).err =
      RoundPoly.evalCoeffs [s.crossLoHi ^^^ m.h0, s.err, s.crossHiLo ^^^ m.h1] rk := by
  show rustDot s.half
        (fun i => padded s.len s.a i ^^^ rustGf128Mul (padded s.len s.a (s.half + i)) rk)
        (fun i => rustGf128Mul (padded s.len s.b i) rk ^^^ padded s.len s.b (s.half + i)) ^^^
      (m.h0 ^^^ rustGf128Mul s.c rk ^^^ rustGf128Mul m.h1 (rustGf128Mul rk rk)) =
    (s.crossLoHi ^^^ m.h0) ^^^ rustGf128Mul rk
      ((rustDot s.len s.a s.b ^^^ s.c) ^^^ rustGf128Mul rk
        ((s.crossHiLo ^^^ m.h1) ^^^ rustGf128Mul rk 0#128))
  rw [rustDot_fold, rustDot_split_half s, rustGf128Mul_zero_right, BitVec.xor_zero]
  unfold IpClaim.crossLoHi IpClaim.crossHiLo
  simp only [rustGf128Mul_xor_left, rustGf128Mul_xor_right, rustGf128Mul_assoc,
    rustGf128Mul_comm, rustGf128Mul_left_comm, BitVec.xor_assoc, BitVec.xor_comm,
    bxor_left_comm]

private theorem two_ne_zero : (2#128 : RustGf128) ≠ 0#128 := by decide
private theorem three_ne_zero : (3#128 : RustGf128) ≠ 0#128 := by decide

/-- A quadratic with a nonzero constant or linear coefficient is not the zero
    function; the witness point is explicit. -/
theorem quadratic_nonzero_point (e0 e1 e2 : RustGf128) (h : e0 ≠ 0#128 ∨ e1 ≠ 0#128) :
    ∃ x : RustGf128, RoundPoly.evalCoeffs [e0, e1, e2] x ≠ CommRingOps.zero := by
  have hEval : ∀ x : RustGf128, RoundPoly.evalCoeffs [e0, e1, e2] x =
      e0 ^^^ rustGf128Mul x (e1 ^^^ rustGf128Mul x e2) := by
    intro x
    show e0 ^^^ rustGf128Mul x (e1 ^^^ rustGf128Mul x (e2 ^^^ rustGf128Mul x 0#128)) = _
    rw [rustGf128Mul_zero_right, BitVec.xor_zero]
  by_cases h0 : e0 = 0#128
  · have h1 : e1 ≠ 0#128 := by
      rcases h with h | h
      · exact absurd h0 h
      · exact h
    subst h0
    by_cases h12 : e1 = e2
    · subst h12
      refine ⟨2#128, ?_⟩
      rw [hEval]
      show 0#128 ^^^ rustGf128Mul 2#128 (e1 ^^^ rustGf128Mul 2#128 e1) ≠ 0#128
      have hThree : e1 ^^^ rustGf128Mul 2#128 e1 = rustGf128Mul 3#128 e1 := by
        rw [show (3#128 : RustGf128) = 1#128 ^^^ 2#128 from by decide, rustGf128Mul_xor_left,
          rustGf128Mul_one_left]
      rw [BitVec.zero_xor, hThree]
      intro hz
      rcases rustGf128Mul_eq_zero _ _ hz with hz | hz
      · exact two_ne_zero hz
      · rcases rustGf128Mul_eq_zero _ _ hz with hz | hz
        · exact three_ne_zero hz
        · exact h1 hz
    · refine ⟨1#128, ?_⟩
      rw [hEval]
      show 0#128 ^^^ rustGf128Mul 1#128 (e1 ^^^ rustGf128Mul 1#128 e2) ≠ 0#128
      rw [BitVec.zero_xor, rustGf128Mul_one_left, rustGf128Mul_one_left]
      intro hz
      apply h12
      have hc := bxor_cancel e1 e2
      rw [hz, BitVec.xor_zero] at hc
      exact hc
  · refine ⟨0#128, ?_⟩
    rw [hEval]
    show e0 ^^^ rustGf128Mul 0#128 (e1 ^^^ rustGf128Mul 0#128 e2) ≠ 0#128
    rw [rustGf128Mul_zero_left, BitVec.xor_zero]
    exact h0

/-- **Fold-round soundness.** With the claim and both cross terms fixed, a
    false claim folds to a true one for at most two coins of any duplicate-free
    sample space. -/
theorem foldRound_false_claim_survives_at_most_two_coins
    (s : IpClaim) (m : FoldMessage) (hErr : s.err ≠ 0#128)
    (S : List RustGf128) (hS : S.Nodup) :
    (S.filter (fun rk => decide ((foldRound s m rk).err = 0#128))).length ≤ 2 := by
  have hCount := RoundPoly.roots_nodup_length_le 2
    [s.crossLoHi ^^^ m.h0, s.err, s.crossHiLo ^^^ m.h1] S hS (Nat.le_refl 3)
    (quadratic_nonzero_point _ _ _ (Or.inr hErr))
  have hPred : (fun rk => decide ((foldRound s m rk).err = 0#128)) =
      (fun r => decide (RoundPoly.evalCoeffs
        [s.crossLoHi ^^^ m.h0, s.err, s.crossHiLo ^^^ m.h1] r = CommRingOps.zero)) := by
    funext rk
    rw [foldRound_err]
    rfl
  rw [hPred]
  exact hCount

/-- A prover that sees the coin first cancels the defect with one cross term. -/
theorem fold_message_after_coin_cancels_defect (s : IpClaim) (rk : RustGf128) :
    (foldRound s ⟨s.crossLoHi ^^^ rustGf128Mul rk s.err, s.crossHiLo⟩ rk).err = 0#128 := by
  rw [foldRound_err]
  show (s.crossLoHi ^^^ (s.crossLoHi ^^^ rustGf128Mul rk s.err)) ^^^ rustGf128Mul rk
    (s.err ^^^ rustGf128Mul rk ((s.crossHiLo ^^^ s.crossHiLo) ^^^ rustGf128Mul rk 0#128)) = 0#128
  rw [bxor_cancel, BitVec.xor_self, rustGf128Mul_zero_right, BitVec.xor_zero,
    rustGf128Mul_zero_right, BitVec.xor_zero, BitVec.xor_self]

/-- Commit order matters: for a false claim, every coin has a forging message
    when the message may be chosen after the coin. -/
theorem tooth_fold_message_after_coin_forges :
    ∃ s : IpClaim, s.err ≠ 0#128 ∧
      ∀ rk : RustGf128, ∃ m : FoldMessage, (foldRound s m rk).err = 0#128 := by
  refine ⟨⟨1, fun _ => 1#128, fun _ => 1#128, 0#128⟩, by decide +kernel, fun rk => ?_⟩
  exact ⟨_, fold_message_after_coin_cancels_defect _ rk⟩

#tooth_pair Qsag.MigrationExecution.foldRound_false_claim_survives_at_most_two_coins vs
  Qsag.MigrationExecution.tooth_fold_message_after_coin_forges

theorem honest_fold_preserves_true_claim (s : IpClaim) (rk : RustGf128)
    (h : s.err = 0#128) :
    (foldRound s ⟨s.crossLoHi, s.crossHiLo⟩ rk).err = 0#128 := by
  rw [foldRound_err, h]
  show (s.crossLoHi ^^^ s.crossLoHi) ^^^ rustGf128Mul rk
    (0#128 ^^^ rustGf128Mul rk ((s.crossHiLo ^^^ s.crossHiLo) ^^^ rustGf128Mul rk 0#128)) = 0#128
  rw [BitVec.xor_self, BitVec.xor_self, rustGf128Mul_zero_right, BitVec.xor_zero,
    rustGf128Mul_zero_right, BitVec.xor_zero, rustGf128Mul_zero_right, BitVec.xor_zero]

/-- Base-case masks and reshared products, fixed before the base coin. -/
structure BaseMessage where
  u : RustGf128
  v : RustGf128
  d1 : RustGf128
  d2 : RustGf128

/-- The opened `gamma = alpha · beta` test on the single remaining pair. -/
def baseAccepts (s : IpClaim) (m : BaseMessage) (rb : RustGf128) : Bool :=
  (baseOpening (s.a 0) (s.b 0) s.c m.u m.v m.d1 m.d2 rb).check

private theorem bxor_eq_zero_iff (x y : RustGf128) : x ^^^ y = 0#128 ↔ x = y := by
  constructor
  · intro h
    have hc := bxor_cancel x y
    rw [h, BitVec.xor_zero] at hc
    exact hc
  · intro h
    rw [h, BitVec.xor_self]

set_option linter.unusedSimpArgs false in
theorem baseAccepts_iff (s : IpClaim) (m : BaseMessage) (rb : RustGf128) (hLen : s.len = 1) :
    baseAccepts s m rb = true ↔
      RoundPoly.evalCoeffs
        [s.err,
         (rustGf128Mul (s.a 0) m.v ^^^ rustGf128Mul m.u (s.b 0)) ^^^ m.d1,
         rustGf128Mul m.u m.v ^^^ m.d2] rb = CommRingOps.zero := by
  have hErr : s.err = rustGf128Mul (s.a 0) (s.b 0) ^^^ s.c := by
    unfold IpClaim.err
    rw [hLen]
    show (0#128 ^^^ rustGf128Mul (s.a 0) (s.b 0)) ^^^ s.c = _
    rw [BitVec.zero_xor]
  have hCheck : baseAccepts s m rb = true ↔
      (s.c ^^^ rustGf128Mul m.d1 rb ^^^ rustGf128Mul m.d2 (rustGf128Mul rb rb)) =
        rustGf128Mul (s.a 0 ^^^ rustGf128Mul m.u rb) (s.b 0 ^^^ rustGf128Mul m.v rb) := by
    unfold baseAccepts BaseOpening.check baseOpening
    exact beq_iff_eq
  rw [hCheck, ← bxor_eq_zero_iff, hErr]
  show _ ↔ (rustGf128Mul (s.a 0) (s.b 0) ^^^ s.c) ^^^ rustGf128Mul rb
      (((rustGf128Mul (s.a 0) m.v ^^^ rustGf128Mul m.u (s.b 0)) ^^^ m.d1) ^^^ rustGf128Mul rb
        ((rustGf128Mul m.u m.v ^^^ m.d2) ^^^ rustGf128Mul rb 0#128)) = 0#128
  rw [rustGf128Mul_zero_right, BitVec.xor_zero]
  simp only [rustGf128Mul_xor_left, rustGf128Mul_xor_right, rustGf128Mul_assoc,
    rustGf128Mul_comm, rustGf128Mul_left_comm, BitVec.xor_assoc, BitVec.xor_comm,
    bxor_left_comm]

/-- **Base-case soundness.** With the masks and reshared products fixed, a
    false single-pair claim passes for at most two base coins. -/
theorem baseAccepts_false_claim_at_most_two_coins
    (s : IpClaim) (m : BaseMessage) (hErr : s.err ≠ 0#128)
    (Sb : List RustGf128) (hSb : Sb.Nodup) :
    (Sb.filter (fun rb => decide (s.len = 1) && baseAccepts s m rb)).length ≤ 2 := by
  by_cases hLen : s.len = 1
  · have hCount := RoundPoly.roots_nodup_length_le 2
      [s.err, (rustGf128Mul (s.a 0) m.v ^^^ rustGf128Mul m.u (s.b 0)) ^^^ m.d1,
        rustGf128Mul m.u m.v ^^^ m.d2] Sb hSb (Nat.le_refl 3)
      (quadratic_nonzero_point _ _ _ (Or.inl hErr))
    have hPred : (fun rb => decide (s.len = 1) && baseAccepts s m rb) =
        (fun r => decide (RoundPoly.evalCoeffs
          [s.err, (rustGf128Mul (s.a 0) m.v ^^^ rustGf128Mul m.u (s.b 0)) ^^^ m.d1,
            rustGf128Mul m.u m.v ^^^ m.d2] r = CommRingOps.zero)) := by
      funext rb
      rw [decide_eq_true hLen]
      show baseAccepts s m rb = _
      cases hb : baseAccepts s m rb
      · exact (decide_eq_false (fun hz => by
          rw [(baseAccepts_iff s m rb hLen).mpr hz] at hb
          cases hb)).symm
      · exact (decide_eq_true ((baseAccepts_iff s m rb hLen).mp hb)).symm
    rw [hPred]
    exact hCount
  · have hPred : (fun rb => decide (s.len = 1) && baseAccepts s m rb) = (fun _ => false) := by
      funext rb
      rw [decide_eq_false hLen]
      rfl
    rw [hPred]
    have hNil : ∀ L : List RustGf128, (L.filter (fun _ => false)).length = 0 := by
      intro L
      induction L with
      | nil => rfl
      | cons x xs ih => simpa only [List.filter] using ih
    rw [hNil]
    omega

theorem honest_base_accepts (s : IpClaim) (u v rb : RustGf128)
    (hLen : s.len = 1) (h : s.err = 0#128) :
    baseAccepts s
      ⟨u, v, rustGf128Mul (s.a 0) v ^^^ rustGf128Mul u (s.b 0), rustGf128Mul u v⟩ rb = true := by
  rw [baseAccepts_iff s _ rb hLen, h]
  show 0#128 ^^^ rustGf128Mul rb
    (((rustGf128Mul (s.a 0) v ^^^ rustGf128Mul u (s.b 0)) ^^^
        (rustGf128Mul (s.a 0) v ^^^ rustGf128Mul u (s.b 0))) ^^^ rustGf128Mul rb
      ((rustGf128Mul u v ^^^ rustGf128Mul u v) ^^^ rustGf128Mul rb 0#128)) = 0#128
  rw [BitVec.xor_self, BitVec.xor_self, rustGf128Mul_zero_right, BitVec.xor_zero,
    rustGf128Mul_zero_right, BitVec.xor_zero, rustGf128Mul_zero_right, BitVec.xor_zero]

/-- An adaptive prover for `r` folds followed by the base case: each message is
    chosen after all earlier coins and before the next one. -/
@[expose] def FoldProver : Nat → Type
  | 0 => BaseMessage
  | r + 1 => FoldMessage × (RustGf128 → FoldProver r)

/-- The verifier's decision on one coin vector (`r` fold coins, then the base
    coin). Wrong-length coin vectors reject. -/
def sacrificeAccepts : (r : Nat) → FoldProver r → IpClaim → List RustGf128 → Bool
  | 0, bm, s, [rb] => decide (s.len = 1) && baseAccepts s bm rb
  | 0, _, _, _ => false
  | _ + 1, _, _, [] => false
  | r + 1, p, s, rk :: rest => sacrificeAccepts r (p.2 rk) (foldRound s p.1 rk) rest

/-- All coin vectors: fold coins from `S`, base coin from `Sb`. -/
def coinVectors (S Sb : List RustGf128) : Nat → List (List RustGf128)
  | 0 => Sb.map (fun rb => [rb])
  | r + 1 => S.flatMap (fun rk => (coinVectors S Sb r).map (fun rest => rk :: rest))

/-- Number of accepting coin vectors, computed along the strategy tree. -/
def acceptingCoins (S Sb : List RustGf128) : (r : Nat) → FoldProver r → IpClaim → Nat
  | 0, bm, s => (Sb.filter (fun rb => decide (s.len = 1) && baseAccepts s bm rb)).length
  | r + 1, p, s =>
    (S.map (fun rk => acceptingCoins S Sb r (p.2 rk) (foldRound s p.1 rk))).sum

private theorem filter_map_length {α β : Type} (f : α → β) (p : β → Bool) : ∀ L : List α,
    ((L.map f).filter p).length = (L.filter (fun x => p (f x))).length
  | [] => rfl
  | x :: xs => by
    have ih := filter_map_length f p xs
    cases hp : p (f x)
    · simpa only [List.map_cons, List.filter, hp] using ih
    · simpa only [List.map_cons, List.filter, hp, List.length_cons, Nat.succ.injEq] using ih

private theorem filter_flatMap_length {α β : Type} (f : α → List β) (p : β → Bool) :
    ∀ L : List α,
      ((L.flatMap f).filter p).length = (L.map (fun x => ((f x).filter p).length)).sum
  | [] => rfl
  | x :: xs => by
    rw [List.flatMap_cons, List.filter_append, List.length_append, List.map_cons, List.sum_cons,
      filter_flatMap_length f p xs]

/-- `acceptingCoins` counts exactly the coin vectors the verifier accepts. -/
theorem acceptingCoins_eq_filter (S Sb : List RustGf128) : ∀ (r : Nat) (p : FoldProver r)
    (s : IpClaim),
    acceptingCoins S Sb r p s =
      ((coinVectors S Sb r).filter (sacrificeAccepts r p s)).length := by
  intro r
  induction r with
  | zero =>
    intro p s
    show (Sb.filter (fun rb => decide (s.len = 1) && baseAccepts s p rb)).length =
      ((Sb.map (fun rb => [rb])).filter (sacrificeAccepts 0 p s)).length
    rw [filter_map_length]
    rfl
  | succ r ih =>
    intro p s
    show (S.map (fun rk => acceptingCoins S Sb r (p.2 rk) (foldRound s p.1 rk))).sum =
      ((S.flatMap (fun rk => (coinVectors S Sb r).map (fun rest => rk :: rest))).filter
        (sacrificeAccepts (r + 1) p s)).length
    rw [filter_flatMap_length]
    congr 1
    apply List.map_congr_left
    intro rk _
    rw [filter_map_length, ih]
    rfl

theorem coinVectors_length (S Sb : List RustGf128) : ∀ r,
    (coinVectors S Sb r).length = S.length ^ r * Sb.length := by
  intro r
  induction r with
  | zero =>
    show (Sb.map (fun rb => [rb])).length = S.length ^ 0 * Sb.length
    rw [List.length_map, Nat.pow_zero, Nat.one_mul]
  | succ r ih =>
    have hSum : ∀ L : List RustGf128,
        (L.flatMap (fun rk => (coinVectors S Sb r).map (fun rest => rk :: rest))).length =
          L.length * (S.length ^ r * Sb.length) := by
      intro L
      induction L with
      | nil => simp only [List.flatMap_nil, List.length_nil, Nat.zero_mul]
      | cons x xs ihL =>
        rw [List.flatMap_cons, List.length_append, List.length_map, ih, ihL, List.length_cons,
          Nat.succ_mul, Nat.add_comm]
    show (S.flatMap (fun rk => (coinVectors S Sb r).map (fun rest => rk :: rest))).length = _
    rw [hSum, Nat.pow_succ, Nat.mul_comm (S.length ^ r) S.length, Nat.mul_assoc]

private theorem sum_map_le_split {α : Type} (bad : α → Bool) (X : α → Nat) (T B : Nat)
    (hT : ∀ x, X x ≤ T) (hB : ∀ x, bad x = false → X x ≤ B) : ∀ L : List α,
    (L.map X).sum ≤ (L.filter bad).length * T + L.length * B
  | [] => by
    show (0 : Nat) ≤ 0 * T + 0 * B
    omega
  | x :: xs => by
    have ih := sum_map_le_split bad X T B hT hB xs
    cases hb : bad x
    · have hx := hB x hb
      simp only [List.map_cons, List.sum_cons, List.filter, hb, List.length_cons, Nat.succ_mul]
      omega
    · have hx := hT x
      simp only [List.map_cons, List.sum_cons, List.filter, hb, List.length_cons, Nat.succ_mul]
      omega

/-- Bad-coin budget for `r` folds: two coin vectors at the base, and per fold
    two bad coins times everything that can follow them. -/
def sacrificeBadCoinBound (n nb : Nat) : Nat → Nat
  | 0 => 2
  | r + 1 => 2 * (n ^ r * nb) + n * sacrificeBadCoinBound n nb r

/-- Closed form, cross-multiplied by one fold-coin count:
    `bound / (n^r · nb) = 2r / n + 2 / nb`. -/
theorem sacrificeBadCoinBound_closed (n nb : Nat) : ∀ r,
    sacrificeBadCoinBound n nb r * n = 2 * r * (n ^ r * nb) + 2 * n ^ (r + 1) := by
  intro r
  induction r with
  | zero =>
    show 2 * n = 2 * 0 * (n ^ 0 * nb) + 2 * n ^ (0 + 1)
    rw [Nat.mul_zero, Nat.zero_mul, Nat.zero_add, Nat.zero_add, Nat.pow_one]
  | succ r ih =>
    show (2 * (n ^ r * nb) + n * sacrificeBadCoinBound n nb r) * n =
      2 * (r + 1) * (n ^ (r + 1) * nb) + 2 * n ^ (r + 1 + 1)
    have hQ : n ^ (r + 1) * nb = n ^ r * nb * n := by
      rw [Nat.pow_succ, Nat.mul_assoc, Nat.mul_assoc, Nat.mul_comm n nb]
    have hW : n ^ (r + 1 + 1) = n * n ^ (r + 1) :=
      (Nat.pow_succ (n := n) (m := r + 1)).trans (Nat.mul_comm _ _)
    rw [hQ, hW]
    generalize n ^ r * nb = P at ih ⊢
    generalize n ^ (r + 1) = W at ih ⊢
    generalize sacrificeBadCoinBound n nb r = B at ih ⊢
    have e1 : (2 * P + n * B) * n = 2 * (P * n) + n * (B * n) := by
      rw [Nat.add_mul, Nat.mul_assoc 2 P n, Nat.mul_assoc n B n]
    have e2 : n * (2 * r * P) = 2 * r * (P * n) := by
      rw [Nat.mul_comm n (2 * r * P), Nat.mul_assoc (2 * r) P n]
    have e3 : n * (2 * W) = 2 * (n * W) := Nat.mul_left_comm n 2 W
    rw [e1, ih, Nat.mul_add n, e2, e3, Nat.mul_add 2 r 1, Nat.add_mul (2 * r) (2 * 1)]
    omega

theorem acceptingCoins_le_total (S Sb : List RustGf128) : ∀ (r : Nat) (p : FoldProver r)
    (s : IpClaim), acceptingCoins S Sb r p s ≤ S.length ^ r * Sb.length := by
  intro r p s
  rw [acceptingCoins_eq_filter, ← coinVectors_length]
  exact List.length_filter_le _ _

/-- **Recursive sacrifice soundness, fresh coins, adaptive prover.** For a
    false inner-product claim and any strategy tree, the accepting coin vectors
    number at most `sacrificeBadCoinBound`: out of `|S|^r · |Sb|` vectors, a
    fraction of at most `2r/|S| + 2/|Sb|`. -/
theorem recursive_sacrifice_false_claim_accepting_coins_bound
    (S Sb : List RustGf128) (hS : S.Nodup) (hSb : Sb.Nodup) :
    ∀ (r : Nat) (p : FoldProver r) (s : IpClaim), s.err ≠ 0#128 →
      acceptingCoins S Sb r p s ≤ sacrificeBadCoinBound S.length Sb.length r := by
  intro r
  induction r with
  | zero =>
    intro p s hErr
    exact baseAccepts_false_claim_at_most_two_coins s p hErr Sb hSb
  | succ r ih =>
    intro p s hErr
    have hSplit := sum_map_le_split
      (fun rk => decide ((foldRound s p.1 rk).err = 0#128))
      (fun rk => acceptingCoins S Sb r (p.2 rk) (foldRound s p.1 rk))
      (S.length ^ r * Sb.length) (sacrificeBadCoinBound S.length Sb.length r)
      (fun rk => acceptingCoins_le_total S Sb r _ _)
      (fun rk hGood => ih (p.2 rk) (foldRound s p.1 rk) (of_decide_eq_false hGood)) S
    have hBad := foldRound_false_claim_survives_at_most_two_coins s p.1 hErr S hS
    have hMul := Nat.mul_le_mul_right (S.length ^ r * Sb.length) hBad
    show (S.map (fun rk => acceptingCoins S Sb r (p.2 rk) (foldRound s p.1 rk))).sum ≤
      2 * (S.length ^ r * Sb.length) + S.length * sacrificeBadCoinBound S.length Sb.length r
    omega

/-- The mutant base case that keeps the length test and drops the opened
    product test. -/
def baseAcceptsWithoutProductTest (s : IpClaim) (_m : BaseMessage) (_rb : RustGf128) : Bool :=
  decide (s.len = 1)

/-- Without the product test a false claim is accepted on every coin, while
    the real base case rejects it. -/
theorem tooth_sacrifice_without_product_test_accepts_false_claim :
    ∃ (s : IpClaim) (m : BaseMessage),
      s.err ≠ 0#128 ∧
      (∀ rb : RustGf128, baseAcceptsWithoutProductTest s m rb = true) ∧
      sacrificeAccepts 0 m s [1#128] = false := by
  refine ⟨⟨1, fun _ => 1#128, fun _ => 1#128, 0#128⟩, ⟨0#128, 0#128, 0#128, 0#128⟩,
    by decide +kernel, fun _ => rfl, by decide +kernel⟩

#tooth_pair Qsag.MigrationExecution.recursive_sacrifice_false_claim_accepting_coins_bound vs
  Qsag.MigrationExecution.tooth_sacrifice_without_product_test_accepts_false_claim

/-- Named acceptance premise for nonvacuity registration. -/
def SacrificeAccepted (r : Nat) (p : FoldProver r) (s : IpClaim)
    (coins : List RustGf128) : Prop :=
  sacrificeAccepts r p s coins = true

theorem sacrifice_accepted_coins_have_round_count (r : Nat) (p : FoldProver r) (s : IpClaim)
    (coins : List RustGf128) (h : SacrificeAccepted r p s coins) : coins.length = r + 1 := by
  induction r generalizing s coins with
  | zero =>
    match coins, h with
    | [_], _ => rfl
    | [], h => cases h
    | _ :: _ :: _, h => cases h
  | succ r ih =>
    match coins, h with
    | [], h => cases h
    | rk :: rest, h =>
      have hr := ih (p.2 rk) (foldRound s p.1 rk) rest h
      rw [List.length_cons, hr]

/-- A true two-element claim is accepted through one honest fold and the
    honest base case. -/
theorem inhabited_sacrifice_accepted :
    ∃ (p : FoldProver 1) (s : IpClaim) (coins : List RustGf128),
      SacrificeAccepted 1 p s coins := by
  refine ⟨(⟨0#128, 0#128⟩, fun _ => ⟨0#128, 0#128, 0#128, 0#128⟩),
    ⟨2, fun _ => 1#128, fun _ => 1#128, 0#128⟩, [1#128, 1#128], ?_⟩
  show sacrificeAccepts 1 _ _ _ = true
  decide +kernel

#verify_inhabited Qsag.MigrationExecution.sacrifice_accepted_coins_have_round_count
  Qsag.MigrationExecution.inhabited_sacrifice_accepted

/-! ### The production flush: two lockstep instances over 64 lanes

`verify_pending_bits_slice` (`outer_mpc.rs:1461-2108`) runs two instances `t ∈ {0, 1}`
of the recursive sacrifice in lockstep on each of the 64 bitsliced lanes. One coin
flip per round yields a coin pair `(r[0], r[1])`; instance `t` of every lane uses
`r[t]` (`outer_mpc.rs:1818-1823`, `2039-2044`). Every reshared message of a round,
for both instances and all lanes, precedes that round's coin flip, and the flush
accepts only if all `2 × 64` base openings pass (`outer_mpc.rs:2091-2105`). The
prover below is one strategy tree for the whole flush, so a message of either
instance may depend on the earlier coins of both. -/

/-- The coins `(r[0], r[1])` drawn by one coin flip. -/
abbrev CoinPair := RustGf128 × RustGf128

def coinAt (rk : CoinPair) (t : Fin 2) : RustGf128 := if t.val = 0 then rk.1 else rk.2

/-- One inner-product claim per instance and lane. -/
abbrev FlushClaims := Fin 2 → Fin 64 → IpClaim

/-- An adaptive prover for the whole flush: all `2 × 64` messages of a round are
    fixed before that round's coin pair. -/
@[expose] def FlushProver : Nat → Type
  | 0 => Fin 2 → Fin 64 → BaseMessage
  | r + 1 => (Fin 2 → Fin 64 → FoldMessage) × (CoinPair → FlushProver r)

def flushFold (cl : FlushClaims) (m : Fin 2 → Fin 64 → FoldMessage) (rk : CoinPair) :
    FlushClaims :=
  fun t lane => foldRound (cl t lane) (m t lane) (coinAt rk t)

/-- All `2 × 64` base cases must pass (`diff_acc`, `outer_mpc.rs:2091-2105`). -/
def flushBaseAccepts (cl : FlushClaims) (bm : Fin 2 → Fin 64 → BaseMessage) (rb : CoinPair) :
    Bool :=
  finAll 2 (fun t => finAll 64 (fun lane =>
    decide ((cl t lane).len = 1) && baseAccepts (cl t lane) (bm t lane) (coinAt rb t)))

/-- The flush base case is the `2 × 64` opening check `checkBaseOpenings`. -/
theorem flushBaseAccepts_checks_all_openings (cl : FlushClaims)
    (bm : Fin 2 → Fin 64 → BaseMessage) (rb : CoinPair)
    (h : flushBaseAccepts cl bm rb = true) :
    checkBaseOpenings (fun t lane =>
      baseOpening ((cl t lane).a 0) ((cl t lane).b 0) (cl t lane).c
        (bm t lane).u (bm t lane).v (bm t lane).d1 (bm t lane).d2 (coinAt rb t)) = true := by
  unfold checkBaseOpenings
  apply (finAll_eq_true_iff 2 _).mpr
  intro t
  apply (finAll_eq_true_iff 64 _).mpr
  intro lane
  have hl : (decide ((cl t lane).len = 1) &&
      baseAccepts (cl t lane) (bm t lane) (coinAt rb t)) = true :=
    (finAll_eq_true_iff 64 _).mp ((finAll_eq_true_iff 2 _).mp h t) lane
  rw [Bool.and_eq_true] at hl
  exact hl.2

private theorem flushBaseAccepts_lane (cl : FlushClaims) (bm : Fin 2 → Fin 64 → BaseMessage)
    (a b : RustGf128) (lane : Fin 64) (h : flushBaseAccepts cl bm (a, b) = true) :
    (decide ((cl 0 lane).len = 1) && baseAccepts (cl 0 lane) (bm 0 lane) a) = true ∧
    (decide ((cl 1 lane).len = 1) && baseAccepts (cl 1 lane) (bm 1 lane) b) = true :=
  ⟨(finAll_eq_true_iff 64 _).mp ((finAll_eq_true_iff 2 _).mp h 0) lane,
    (finAll_eq_true_iff 64 _).mp ((finAll_eq_true_iff 2 _).mp h 1) lane⟩

/-- The flush verifier's decision on one vector of coin pairs. -/
def flushAccepts : (r : Nat) → FlushProver r → FlushClaims → List CoinPair → Bool
  | 0, bm, cl, [rb] => flushBaseAccepts cl bm rb
  | 0, _, _, _ => false
  | _ + 1, _, _, [] => false
  | r + 1, p, cl, rk :: rest => flushAccepts r (p.2 rk) (flushFold cl p.1 rk) rest

def coinPairs (L : List RustGf128) : List CoinPair :=
  L.flatMap (fun a => L.map (fun b => (a, b)))

/-- All coin-pair vectors: fold pairs from `S × S`, the base pair from `Sb × Sb`. -/
def flushCoinVectors (S Sb : List RustGf128) : Nat → List (List CoinPair)
  | 0 => (coinPairs Sb).map (fun rb => [rb])
  | r + 1 => (coinPairs S).flatMap (fun rk => (flushCoinVectors S Sb r).map (fun rest => rk :: rest))

/-- Number of accepting coin-pair vectors, computed along the strategy tree. -/
def flushAccepting (S Sb : List RustGf128) : (r : Nat) → FlushProver r → FlushClaims → Nat
  | 0, bm, cl => ((coinPairs Sb).filter (fun rb => flushBaseAccepts cl bm rb)).length
  | r + 1, p, cl =>
    ((coinPairs S).map (fun rk => flushAccepting S Sb r (p.2 rk) (flushFold cl p.1 rk))).sum

/-- `flushAccepting` counts exactly the coin-pair vectors the flush verifier accepts. -/
theorem flushAccepting_eq_filter (S Sb : List RustGf128) : ∀ (r : Nat) (p : FlushProver r)
    (cl : FlushClaims),
    flushAccepting S Sb r p cl =
      ((flushCoinVectors S Sb r).filter (flushAccepts r p cl)).length := by
  intro r
  induction r with
  | zero =>
    intro p cl
    show ((coinPairs Sb).filter (fun rb => flushBaseAccepts cl p rb)).length =
      (((coinPairs Sb).map (fun rb => [rb])).filter (flushAccepts 0 p cl)).length
    rw [filter_map_length]
    rfl
  | succ r ih =>
    intro p cl
    show ((coinPairs S).map (fun rk => flushAccepting S Sb r (p.2 rk) (flushFold cl p.1 rk))).sum =
      (((coinPairs S).flatMap (fun rk => (flushCoinVectors S Sb r).map (fun rest => rk :: rest))).filter
        (flushAccepts (r + 1) p cl)).length
    rw [filter_flatMap_length]
    congr 1
    apply List.map_congr_left
    intro rk _
    rw [filter_map_length, ih]
    rfl

private theorem flatMap_map_length {α β γ : Type} (V : List β) (f : α → β → γ) : ∀ L : List α,
    (L.flatMap (fun x => V.map (f x))).length = L.length * V.length
  | [] => by
    show (0 : Nat) = 0 * V.length
    rw [Nat.zero_mul]
  | x :: xs => by
    rw [List.flatMap_cons, List.length_append, List.length_map, flatMap_map_length V f xs,
      List.length_cons, Nat.succ_mul, Nat.add_comm]

theorem coinPairs_length (L : List RustGf128) : (coinPairs L).length = L.length * L.length :=
  flatMap_map_length L (fun a b => (a, b)) L

/-- The coin space of one flush has `(|S|^r · |Sb|)²` points. -/
theorem flushCoinVectors_length (S Sb : List RustGf128) : ∀ r,
    (flushCoinVectors S Sb r).length =
      (S.length ^ r * Sb.length) * (S.length ^ r * Sb.length) := by
  intro r
  induction r with
  | zero =>
    show ((coinPairs Sb).map (fun rb => [rb])).length = _
    rw [List.length_map, coinPairs_length, Nat.pow_zero, Nat.one_mul]
  | succ r ih =>
    show ((coinPairs S).flatMap
      (fun rk => (flushCoinVectors S Sb r).map (fun rest => rk :: rest))).length = _
    rw [flatMap_map_length (flushCoinVectors S Sb r) (fun rk rest => rk :: rest), coinPairs_length,
      ih, Nat.pow_succ]
    generalize S.length ^ r = q
    generalize S.length = n
    generalize Sb.length = nb
    simp only [Nat.mul_comm, Nat.mul_left_comm]

private theorem filter_length_le_of_imp {α : Type} (p q : α → Bool)
    (h : ∀ x, p x = true → q x = true) : ∀ L : List α,
    (L.filter p).length ≤ (L.filter q).length
  | [] => Nat.le_refl _
  | x :: xs => by
    have ih := filter_length_le_of_imp p q h xs
    cases hp : p x
    · cases hq : q x
      · simpa only [List.filter, hp, hq] using ih
      · simp only [List.filter, hp, hq, List.length_cons]
        omega
    · simp only [List.filter, hp, h x hp, List.length_cons]
      omega

private theorem filter_false_length {α : Type} : ∀ L : List α,
    (L.filter (fun _ => false)).length = 0
  | [] => rfl
  | _ :: xs => by simpa only [List.filter] using filter_false_length xs

private theorem sum_map_le_sum_map {α : Type} (f g : α → Nat) (h : ∀ x, f x ≤ g x) :
    ∀ L : List α, (L.map f).sum ≤ (L.map g).sum
  | [] => Nat.le_refl _
  | x :: xs => by
    have ih := sum_map_le_sum_map f g h xs
    have hx := h x
    show f x + (xs.map f).sum ≤ g x + (xs.map g).sum
    omega

private theorem sum_map_le_cases {α : Type} (bad : α → Bool) (X : α → Nat) (T B : Nat)
    (hT : ∀ x, bad x = true → X x ≤ T) (hB : ∀ x, bad x = false → X x ≤ B) : ∀ L : List α,
    (L.map X).sum ≤ (L.filter bad).length * T + L.length * B
  | [] => by
    show (0 : Nat) ≤ 0 * T + 0 * B
    omega
  | x :: xs => by
    have ih := sum_map_le_cases bad X T B hT hB xs
    cases hb : bad x
    · have hx := hB x hb
      simp only [List.map_cons, List.sum_cons, List.filter, hb, List.length_cons, Nat.succ_mul]
      omega
    · have hx := hT x hb
      simp only [List.map_cons, List.sum_cons, List.filter, hb, List.length_cons, Nat.succ_mul]
      omega

private theorem sum_map_const_mul {β : Type} (c : Nat) (g : β → Nat) : ∀ M : List β,
    (M.map (fun b => c * g b)).sum = c * (M.map g).sum
  | [] => by
    show (0 : Nat) = c * 0
    rw [Nat.mul_zero]
  | y :: ys => by
    show c * g y + (ys.map (fun b => c * g b)).sum = c * (g y + (ys.map g).sum)
    rw [sum_map_const_mul c g ys, Nat.mul_add]

private theorem sum_sum_mul {α β : Type} (f : α → Nat) (g : β → Nat) (M : List β) :
    ∀ L : List α,
      (L.map (fun a => (M.map (fun b => f a * g b)).sum)).sum = (L.map f).sum * (M.map g).sum
  | [] => by
    show (0 : Nat) = 0 * (M.map g).sum
    rw [Nat.zero_mul]
  | x :: xs => by
    show (M.map (fun b => f x * g b)).sum +
        (xs.map (fun a => (M.map (fun b => f a * g b)).sum)).sum =
      (f x + (xs.map f).sum) * (M.map g).sum
    rw [sum_sum_mul f g M xs, sum_map_const_mul (f x) g M, Nat.add_mul]

private theorem sum_map_append {α : Type} (f : α → Nat) : ∀ A B : List α,
    ((A ++ B).map f).sum = (A.map f).sum + (B.map f).sum
  | [], B => by
    show (B.map f).sum = 0 + (B.map f).sum
    rw [Nat.zero_add]
  | x :: xs, B => by
    show f x + ((xs ++ B).map f).sum = f x + (xs.map f).sum + (B.map f).sum
    rw [sum_map_append f xs B, Nat.add_assoc]

private theorem sum_map_pairs (f : CoinPair → Nat) (M : List RustGf128) :
    ∀ L : List RustGf128,
      ((L.flatMap (fun a => M.map (fun b => (a, b)))).map f).sum =
        (L.map (fun a => (M.map (fun b => f (a, b))).sum)).sum
  | [] => rfl
  | a :: as => by
    rw [List.flatMap_cons, sum_map_append, sum_map_pairs f M as, List.map_map]
    rfl

private theorem filter_pairs_length (q : CoinPair → Bool) (M : List RustGf128) :
    ∀ L : List RustGf128,
      ((L.flatMap (fun a => M.map (fun b => (a, b)))).filter q).length =
        (L.map (fun a => (M.filter (fun b => q (a, b))).length)).sum := by
  intro L
  rw [filter_flatMap_length]
  congr 1
  apply List.map_congr_left
  intro a _
  exact filter_map_length _ q M

/-- Per-instance budget: the single-instance bad-coin bound when the claim is known
    false, the whole coin space otherwise. -/
private def laneWeight (n nb : Nat) (known : Bool) (r : Nat) : Nat :=
  cond known (sacrificeBadCoinBound n nb r) (n ^ r * nb)

private def foldedWeight (S Sb : List RustGf128) (s : IpClaim) (m : FoldMessage) (k : Bool)
    (r : Nat) (rk : RustGf128) : Nat :=
  laneWeight S.length Sb.length (k && decide ((foldRound s m rk).err ≠ 0#128)) r

private theorem foldedWeight_sum_le (S Sb : List RustGf128) (hS : S.Nodup) (s : IpClaim)
    (m : FoldMessage) (k : Bool) (hk : k = true → s.err ≠ 0#128) (r : Nat) :
    (S.map (foldedWeight S Sb s m k r)).sum ≤ laneWeight S.length Sb.length k (r + 1) := by
  cases k with
  | true =>
    have hErr := hk rfl
    have hT : ∀ rk, decide ((foldRound s m rk).err = 0#128) = true →
        foldedWeight S Sb s m true r rk ≤ S.length ^ r * Sb.length := by
      intro rk hb
      have hd : decide ((foldRound s m rk).err ≠ 0#128) = false :=
        decide_eq_false (fun hne => hne (of_decide_eq_true hb))
      show laneWeight S.length Sb.length (true && decide ((foldRound s m rk).err ≠ 0#128)) r ≤ _
      rw [hd]
      exact Nat.le_refl _
    have hB : ∀ rk, decide ((foldRound s m rk).err = 0#128) = false →
        foldedWeight S Sb s m true r rk ≤ sacrificeBadCoinBound S.length Sb.length r := by
      intro rk hg
      have hd : decide ((foldRound s m rk).err ≠ 0#128) = true :=
        decide_eq_true (of_decide_eq_false hg)
      show laneWeight S.length Sb.length (true && decide ((foldRound s m rk).err ≠ 0#128)) r ≤ _
      rw [hd]
      exact Nat.le_refl _
    have hSplit := sum_map_le_cases (fun rk => decide ((foldRound s m rk).err = 0#128))
      (foldedWeight S Sb s m true r) (S.length ^ r * Sb.length)
      (sacrificeBadCoinBound S.length Sb.length r) hT hB S
    have hBad := foldRound_false_claim_survives_at_most_two_coins s m hErr S hS
    have hMul := Nat.mul_le_mul_right (S.length ^ r * Sb.length) hBad
    show (S.map (foldedWeight S Sb s m true r)).sum ≤
      2 * (S.length ^ r * Sb.length) + S.length * sacrificeBadCoinBound S.length Sb.length r
    omega
  | false =>
    have hSplit := sum_map_le_cases (fun _ : RustGf128 => false)
      (foldedWeight S Sb s m false r) 0 (S.length ^ r * Sb.length)
      (fun _ hb => nomatch hb) (fun _ _ => Nat.le_refl _) S
    show (S.map (foldedWeight S Sb s m false r)).sum ≤ S.length ^ (r + 1) * Sb.length
    rw [Nat.pow_succ, Nat.mul_comm (S.length ^ r) S.length, Nat.mul_assoc]
    omega

private theorem flushAccepting_le_weights (S Sb : List RustGf128) (hS : S.Nodup)
    (hSb : Sb.Nodup) (lane : Fin 64) :
    ∀ (r : Nat) (p : FlushProver r) (cl : FlushClaims) (k0 k1 : Bool),
      (k0 = true → (cl 0 lane).err ≠ 0#128) → (k1 = true → (cl 1 lane).err ≠ 0#128) →
      flushAccepting S Sb r p cl ≤
        laneWeight S.length Sb.length k0 r * laneWeight S.length Sb.length k1 r := by
  intro r
  induction r with
  | zero =>
    intro p cl k0 k1 h0 h1
    have hCount : flushAccepting S Sb 0 p cl =
        (Sb.map (fun a => (Sb.filter (fun b => flushBaseAccepts cl p (a, b))).length)).sum :=
      filter_pairs_length (fun rb => flushBaseAccepts cl p rb) Sb Sb
    have hInner : ∀ a, (Sb.filter (fun b => flushBaseAccepts cl p (a, b))).length ≤
        (Sb.filter (fun b =>
          decide ((cl 1 lane).len = 1) && baseAccepts (cl 1 lane) (p 1 lane) b)).length :=
      fun a => filter_length_le_of_imp _ _
        (fun b hb => (flushBaseAccepts_lane cl p a b lane hb).2) Sb
    have hZero : ∀ a,
        (decide ((cl 0 lane).len = 1) && baseAccepts (cl 0 lane) (p 0 lane) a) = false →
        (Sb.filter (fun b => flushBaseAccepts cl p (a, b))).length ≤ 0 := by
      intro a ha
      have hle := filter_length_le_of_imp (fun b => flushBaseAccepts cl p (a, b))
        (fun _ => false)
        (fun b hb => nomatch (flushBaseAccepts_lane cl p a b lane hb).1.symm.trans ha) Sb
      rw [filter_false_length] at hle
      exact hle
    have hSplit := sum_map_le_cases
      (fun a => decide ((cl 0 lane).len = 1) && baseAccepts (cl 0 lane) (p 0 lane) a)
      (fun a => (Sb.filter (fun b => flushBaseAccepts cl p (a, b))).length)
      (Sb.filter (fun b =>
        decide ((cl 1 lane).len = 1) && baseAccepts (cl 1 lane) (p 1 lane) b)).length 0
      (fun a _ => hInner a) hZero Sb
    have hC0 : (Sb.filter (fun a =>
        decide ((cl 0 lane).len = 1) && baseAccepts (cl 0 lane) (p 0 lane) a)).length ≤
        laneWeight S.length Sb.length k0 0 := by
      cases k0 with
      | true => exact baseAccepts_false_claim_at_most_two_coins (cl 0 lane) (p 0 lane) (h0 rfl) Sb hSb
      | false =>
        show _ ≤ S.length ^ 0 * Sb.length
        rw [Nat.pow_zero, Nat.one_mul]
        exact List.length_filter_le _ _
    have hC1 : (Sb.filter (fun b =>
        decide ((cl 1 lane).len = 1) && baseAccepts (cl 1 lane) (p 1 lane) b)).length ≤
        laneWeight S.length Sb.length k1 0 := by
      cases k1 with
      | true => exact baseAccepts_false_claim_at_most_two_coins (cl 1 lane) (p 1 lane) (h1 rfl) Sb hSb
      | false =>
        show _ ≤ S.length ^ 0 * Sb.length
        rw [Nat.pow_zero, Nat.one_mul]
        exact List.length_filter_le _ _
    rw [hCount]
    exact Nat.le_trans hSplit (by
      rw [Nat.mul_zero, Nat.add_zero]
      exact Nat.mul_le_mul hC0 hC1)
  | succ r ih =>
    intro p cl k0 k1 h0 h1
    have hCount : flushAccepting S Sb (r + 1) p cl =
        (S.map (fun a => (S.map (fun b =>
          flushAccepting S Sb r (p.2 (a, b)) (flushFold cl p.1 (a, b)))).sum)).sum :=
      sum_map_pairs (fun rk => flushAccepting S Sb r (p.2 rk) (flushFold cl p.1 rk)) S S
    have hIH : ∀ a b, flushAccepting S Sb r (p.2 (a, b)) (flushFold cl p.1 (a, b)) ≤
        foldedWeight S Sb (cl 0 lane) (p.1 0 lane) k0 r a *
          foldedWeight S Sb (cl 1 lane) (p.1 1 lane) k1 r b := by
      intro a b
      refine ih (p.2 (a, b)) (flushFold cl p.1 (a, b))
        (k0 && decide ((foldRound (cl 0 lane) (p.1 0 lane) a).err ≠ 0#128))
        (k1 && decide ((foldRound (cl 1 lane) (p.1 1 lane) b).err ≠ 0#128)) ?_ ?_
      · intro hk
        rw [Bool.and_eq_true] at hk
        exact of_decide_eq_true hk.2
      · intro hk
        rw [Bool.and_eq_true] at hk
        exact of_decide_eq_true hk.2
    rw [hCount]
    calc (S.map (fun a => (S.map (fun b =>
            flushAccepting S Sb r (p.2 (a, b)) (flushFold cl p.1 (a, b)))).sum)).sum
        ≤ (S.map (fun a => (S.map (fun b =>
            foldedWeight S Sb (cl 0 lane) (p.1 0 lane) k0 r a *
              foldedWeight S Sb (cl 1 lane) (p.1 1 lane) k1 r b)).sum)).sum :=
          sum_map_le_sum_map _ _ (fun a => sum_map_le_sum_map _ _ (fun b => hIH a b) S) S
      _ = (S.map (foldedWeight S Sb (cl 0 lane) (p.1 0 lane) k0 r)).sum *
            (S.map (foldedWeight S Sb (cl 1 lane) (p.1 1 lane) k1 r)).sum :=
          sum_sum_mul _ _ S S
      _ ≤ laneWeight S.length Sb.length k0 (r + 1) * laneWeight S.length Sb.length k1 (r + 1) :=
          Nat.mul_le_mul (foldedWeight_sum_le S Sb hS _ _ k0 h0 r)
            (foldedWeight_sum_le S Sb hS _ _ k1 h1 r)

/-- **Two-instance, 64-lane flush soundness, fresh coin pairs, adaptive prover.** If
    both instances' inner-product claims of one lane are false, then for any flush
    strategy tree the accepting coin-pair vectors number at most
    `sacrificeBadCoinBound²`: out of `(|S|^r · |Sb|)²` vectors, a fraction of at most
    `(2r/|S| + 2/|Sb|)²`. The other 63 lanes and the cross-instance adaptivity do not
    help the prover. -/
theorem flush_false_lane_accepting_coins_bound
    (S Sb : List RustGf128) (hS : S.Nodup) (hSb : Sb.Nodup) (r : Nat) (p : FlushProver r)
    (cl : FlushClaims) (lane : Fin 64)
    (h0 : (cl 0 lane).err ≠ 0#128) (h1 : (cl 1 lane).err ≠ 0#128) :
    flushAccepting S Sb r p cl ≤
      sacrificeBadCoinBound S.length Sb.length r * sacrificeBadCoinBound S.length Sb.length r :=
  flushAccepting_le_weights S Sb hS hSb lane r p cl true true (fun _ => h0) (fun _ => h1)

/-- With only instance `0` of the lane false, the bound is the single-instance one
    times the whole coin space of the other instance. -/
theorem flush_one_false_instance_accepting_coins_bound
    (S Sb : List RustGf128) (hS : S.Nodup) (hSb : Sb.Nodup) (r : Nat) (p : FlushProver r)
    (cl : FlushClaims) (lane : Fin 64) (h0 : (cl 0 lane).err ≠ 0#128) :
    flushAccepting S Sb r p cl ≤
      sacrificeBadCoinBound S.length Sb.length r * (S.length ^ r * Sb.length) :=
  flushAccepting_le_weights S Sb hS hSb lane r p cl true false (fun _ => h0) (fun h => nomatch h)

/-- The mutant base case that checks lane `0` only. -/
def flushBaseAcceptsLaneZeroOnly (cl : FlushClaims) (bm : Fin 2 → Fin 64 → BaseMessage)
    (rb : CoinPair) : Bool :=
  finAll 2 (fun t => decide ((cl t 0).len = 1) && baseAccepts (cl t 0) (bm t 0) (coinAt rb t))

/-- Checking one lane lets a false claim in another lane through; the real base
    case rejects it. -/
theorem tooth_flush_single_lane_check_accepts_false_lane :
    ∃ (cl : FlushClaims) (bm : Fin 2 → Fin 64 → BaseMessage) (lane : Fin 64) (rb : CoinPair),
      (cl 0 lane).err ≠ 0#128 ∧ (cl 1 lane).err ≠ 0#128 ∧
      flushBaseAcceptsLaneZeroOnly cl bm rb = true ∧
      flushBaseAccepts cl bm rb = false := by
  refine ⟨fun _ lane => ⟨1, fun _ => 1#128, fun _ => 1#128, if lane.val = 0 then 1#128 else 0#128⟩,
    fun _ _ => ⟨0#128, 0#128, 0#128, 0#128⟩, 1, (1#128, 1#128),
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

#tooth_pair Qsag.MigrationExecution.flush_false_lane_accepting_coins_bound vs
  Qsag.MigrationExecution.tooth_flush_single_lane_check_accepts_false_lane

/-- Public statement fields stay separate; epoch is bounded rather than an
    unbounded natural silently truncated by a serializer. Authorization must bind
    this entire statement, including the destination. -/
structure Statement where
  legacyCommitment : List UInt8
  migrationDomain : BitVec 256
  nullifier : BitVec 256
  destination : BitVec 256
  epoch : UInt64
  deriving DecidableEq

/-- Collision-aware ownership relation. `derivePoint` must be instantiated with
    a verified curve implementation, and `address` with the selected legacy
    commitment (HASH160, Keccak20, or parity-checked x-only encoding).
    Unlike the transparent scalar zero test, this relation includes BOTH the
    address commitment and the campaign nullifier. -/
def Ownership {Point Address : Type}
    (derivePoint : MigrationKey256 → Point) (address : Point → Address)
    (nullifier : MigrationKey256 → BitVec 256 → BitVec 256)
    (group : ScalarGroup) (expected : Address) (statement : Statement)
    (secret : MigrationKey256) : Prop :=
  requireCanonicalScalar group secret = true ∧
  address (derivePoint secret) = expected ∧
  nullifier secret statement.migrationDomain = statement.nullifier

/-- Hash-address acceptance cannot imply unconditional zero fault. This theorem
    retains the collision alternative for the *joint* address/nullifier map,
    without asserting that an address collision alone is a migration forgery. -/
theorem ownership_same_witness_or_joint_collision {Point Address : Type}
    (derivePoint : MigrationKey256 → Point) (address : Point → Address)
    (nullifier : MigrationKey256 → BitVec 256 → BitVec 256)
    (group : ScalarGroup) (expected : Address) (statement : Statement)
    (s t : MigrationKey256)
    (hs : Ownership derivePoint address nullifier group expected statement s)
    (ht : Ownership derivePoint address nullifier group expected statement t) :
    s = t ∨ (s ≠ t ∧
      (address (derivePoint s), nullifier s statement.migrationDomain) =
      (address (derivePoint t), nullifier t statement.migrationDomain)) := by
  by_cases h : s = t
  · exact Or.inl h
  · exact Or.inr ⟨h, Prod.ext (hs.2.1.trans ht.2.1.symm)
      (hs.2.2.trans ht.2.2.symm)⟩

/-- A small-range hash counterexample. The two witnesses are canonical but
    neither address nor nullifier binding follows for arbitrary hash functions. -/
theorem tooth_constant_hashes_do_not_bind_witness :
    ∃ statement : Statement,
      Ownership id (fun _ : MigrationKey256 => false) (fun _ _ => 0#256)
        .Secp256k1 false statement 1#256 ∧
      Ownership id (fun _ : MigrationKey256 => false) (fun _ _ => 0#256)
        .Secp256k1 false statement 2#256 ∧
      (1#256 : MigrationKey256) ≠ 2#256 := by
  refine ⟨⟨[], 0#256, 0#256, 1#256, 0⟩, ?_, ?_, by decide⟩ <;>
    constructor
  · decide
  · exact ⟨rfl, rfl⟩
  · decide
  · exact ⟨rfl, rfl⟩

#tooth_pair Qsag.MigrationExecution.ownership_same_witness_or_joint_collision vs
  Qsag.MigrationExecution.tooth_constant_hashes_do_not_bind_witness

/-- A pending multiplication contains the same shares consumed and emitted by
    the gate evaluator. There is no independently supplied triple list. -/
structure PendingAnd where
  lhs : RssWord64Shares3
  rhs : RssWord64Shares3
  output : RssWord64Shares3
  deriving DecidableEq

/-- Exact reference check, over all 64 Boolean lanes. This is intentionally NOT
    advertised as the private or batched BBCGGI19 implementation. -/
def PendingAnd.check (t : PendingAnd) : Bool :=
  t.output.reconstruct == (t.lhs.reconstruct &&& t.rhs.reconstruct)

/-- Indices refer to existing wires; outputs are prepended. An AND consumes the
    adversarially supplied result, so corrupting it affects all following gates. -/
inductive Gate where
  | xor (lhs rhs : Nat)
  | and (lhs rhs : Nat) (output : RssWord64Shares3)
  deriving DecidableEq

structure GateState where
  wires : List RssWord64Shares3
  pending : List PendingAnd
  deriving DecidableEq

def xorShares (a b : RssWord64Shares3) : RssWord64Shares3 :=
  ⟨a.w0 ^^^ b.w0, a.w1 ^^^ b.w1, a.w2 ^^^ b.w2⟩

def evalGate (st : GateState) (gate : Gate) : Option GateState := do
  match gate with
  | .xor l r =>
    let a ← st.wires[l]?
    let b ← st.wires[r]?
    return { st with wires := xorShares a b :: st.wires }
  | .and l r output =>
    let a ← st.wires[l]?
    let b ← st.wires[r]?
    return { wires := output :: st.wires
             pending := ⟨a, b, output⟩ :: st.pending }

def evalGates : GateState → List Gate → Option GateState
  | st, [] => some st
  | st, g :: gs => (evalGate st g).bind (fun next => evalGates next gs)

def witnessWires (witness : RssWitnessLanes3) : List RssWord64Shares3 :=
  List.ofFn (fun i : Fin 256 => ⟨witness.w0 i, witness.w1 i, witness.w2 i⟩)

inductive ExecutionResult where
  | invalidLanes
  | invalidWire
  | multiplicationCheck
  | invalidProof
  | accepted
  deriving Repr, DecidableEq

/-- Open the evaluated final gate only AFTER checking every pending AND. -/
def finish (st : GateState) : ExecutionResult :=
  if st.pending.all PendingAnd.check then
    match st.wires with
    | [] => .invalidWire
    | out :: _ => if out.reconstruct == 0xFFFFFFFFFFFFFFFF then .accepted else .invalidProof
  else .multiplicationCheck

/-- This trace evaluator is the executable reference boundary. It checks all
    256 × 3 input lane words and uses those exact words as circuit inputs. The
    trusted circuit compiler must supply the ownership/zero-test circuit; an
    arbitrary circuit alone does not establish ownership. -/
def run (witness : RssWitnessLanes3) (gates : List Gate) : ExecutionResult :=
  if shareUniformLanesCheck witness then
    match evalGates ⟨witnessWires witness, []⟩ gates with
    | none => .invalidWire
    | some st => finish st
  else .invalidLanes

theorem finish_checks_consumed_outputs (st : GateState)
    (h : finish st = .accepted) :
    ∀ t ∈ st.pending,
      t.output.reconstruct = (t.lhs.reconstruct &&& t.rhs.reconstruct) := by
  unfold finish at h
  cases hp : st.pending.all PendingAnd.check
  · rw [hp] at h
    cases h
  · intro t ht
    exact eq_of_beq (List.all_eq_true.mp hp t ht)

/-- Every accepted run checked the ACTUAL witness lane words, not a free mask. -/
theorem run_checks_actual_lanes (witness : RssWitnessLanes3) (gates : List Gate)
    (h : run witness gates = .accepted) : shareUniformLanesCheck witness = true := by
  cases hl : shareUniformLanesCheck witness
  · simp only [run, hl, Bool.false_eq_true, ↓reduceIte] at h
    cases h
  · rfl

/-- Acceptance connects lane validation, the concrete evaluator result, and
    every pending multiplication to one execution. -/
theorem run_has_checked_execution (witness : RssWitnessLanes3) (gates : List Gate)
    (h : run witness gates = .accepted) :
    shareUniformLanesCheck witness = true ∧
    ∃ st : GateState,
      evalGates ⟨witnessWires witness, []⟩ gates = some st ∧
      finish st = .accepted ∧
      ∀ t ∈ st.pending,
        t.output.reconstruct = (t.lhs.reconstruct &&& t.rhs.reconstruct) := by
  have hl := run_checks_actual_lanes witness gates h
  refine ⟨hl, ?_⟩
  unfold run at h
  rw [hl] at h
  cases he : evalGates ⟨witnessWires witness, []⟩ gates with
  | none =>
    rw [he] at h
    cases h
  | some st =>
    rw [he] at h
    exact ⟨st, rfl, h, finish_checks_consumed_outputs st h⟩

theorem accepted_execution_same_witness_in_every_lane
    (witness : RssWitnessLanes3) (gates : List Gate)
    (h : run witness gates = .accepted) (a b : Fin 64) :
    extractRepetitionWitness witness a.val = extractRepetitionWitness witness b.val :=
  shareUniformLanesCheck_implies_uniform_witness_across_lanes.1 witness
    (run_checks_actual_lanes witness gates h) a.val b.val a.isLt b.isLt

/-- Removing precisely the linked multiplication barrier accepts the corrupted
    final AND output. This is a whole evaluator path, not an unrelated triple. -/
def finishWithoutCheck (st : GateState) : ExecutionResult :=
  match st.wires with
  | [] => .invalidWire
  | out :: _ => if out.reconstruct == 0xFFFFFFFFFFFFFFFF then .accepted else .invalidProof

theorem tooth_corrupt_final_and_guard_removal :
    ∃ initial : GateState, ∃ gates : List Gate, ∃ evaluated : GateState,
      evalGates initial gates = some evaluated ∧
      finish evaluated = .multiplicationCheck ∧
      finishWithoutCheck evaluated = .accepted ∧
      ∃ t ∈ evaluated.pending,
        t.output.reconstruct ≠ (t.lhs.reconstruct &&& t.rhs.reconstruct) := by
  let zero : RssWord64Shares3 := ⟨0, 0, 0⟩
  let forged : RssWord64Shares3 := ⟨0xFFFFFFFFFFFFFFFF, 0, 0⟩
  refine ⟨⟨[zero], []⟩, [.and 0 0 forged],
    ⟨[forged, zero], [⟨zero, zero, forged⟩]⟩, rfl, ?_, ?_,
    ⟨zero, zero, forged⟩, .head _, ?_⟩ <;> decide

#tooth_pair Qsag.MigrationExecution.finish_checks_consumed_outputs vs
  Qsag.MigrationExecution.tooth_corrupt_final_and_guard_removal

/-- Persistent spent set (represented as a duplicate-free list when started
    empty). Settlement never removes an entry, including on rejection. -/
structure Ledger where
  spent : List (BitVec 256)
  deriving DecidableEq

structure Submission (Authorization : Type) where
  statement : Statement
  authorization : Authorization
  witness : RssWitnessLanes3

inductive SettlementResult where
  | accepted
  | replay
  | unauthorized
  | executionRejected (reason : ExecutionResult)
  deriving Repr, DecidableEq

/-- The circuit comes from the verifier's compiler, not the submission. The
    authorization verifier receives every statement field. Replay checking and
    insertion are one transition; invalid authorization/execution burns nothing.
    This models logical persistence, not a filesystem crash-consistency proof. -/
def settle {Authorization : Type}
    (verifyAuthorization : Statement → Authorization → Bool)
    (compile : Statement → List Gate)
    (ledger : Ledger) (submission : Submission Authorization) : Ledger × SettlementResult :=
  if submission.statement.nullifier ∈ ledger.spent then (ledger, .replay)
  else if verifyAuthorization submission.statement submission.authorization then
    match run submission.witness (compile submission.statement) with
    | .accepted => (⟨submission.statement.nullifier :: ledger.spent⟩, .accepted)
    | reason => (ledger, .executionRejected reason)
  else (ledger, .unauthorized)

/-- Replay rejects deterministically, independent of the new destination,
    authorization, circuit, witness, or errors it would have produced. -/
theorem settle_replay_rejected {Authorization : Type}
    (verifyAuthorization : Statement → Authorization → Bool)
    (compile : Statement → List Gate)
    (ledger : Ledger) (submission : Submission Authorization)
    (h : submission.statement.nullifier ∈ ledger.spent) :
    settle verifyAuthorization compile ledger submission = (ledger, .replay) := by
  unfold settle
  rw [cIte_pos h]

/-- An accepted transition inserts exactly the checked nullifier. -/
theorem settle_accept_inserts {Authorization : Type}
    (verifyAuthorization : Statement → Authorization → Bool)
    (compile : Statement → List Gate)
    (ledger : Ledger) (submission : Submission Authorization)
    (h : (settle verifyAuthorization compile ledger submission).2 = .accepted) :
    (settle verifyAuthorization compile ledger submission).1.spent =
      submission.statement.nullifier :: ledger.spent := by
  unfold settle at h ⊢
  cases (inferInstance : Decidable (submission.statement.nullifier ∈ ledger.spent)) with
  | isTrue hMem =>
    rw [cIte_pos hMem] at h
    cases h
  | isFalse hMem =>
    rw [cIte_neg hMem] at h ⊢
    cases hAuth : verifyAuthorization submission.statement submission.authorization
    · simp only [hAuth, Bool.false_eq_true, ↓reduceIte] at h
      cases h
    · simp only [hAuth, ↓reduceIte] at h ⊢
      cases hr : run submission.witness (compile submission.statement) <;>
        simp only [hr] at h ⊢ <;> first | rfl | cases h

theorem settle_spent_monotone {Authorization : Type}
    (verifyAuthorization : Statement → Authorization → Bool)
    (compile : Statement → List Gate)
    (ledger : Ledger) (submission : Submission Authorization)
    (n : BitVec 256) (hn : n ∈ ledger.spent) :
    n ∈ (settle verifyAuthorization compile ledger submission).1.spent := by
  unfold settle
  split
  · exact hn
  · split
    · cases run submission.witness (compile submission.statement) <;>
        first | exact hn | exact List.mem_cons_of_mem _ hn
    · exact hn

/-- The complete settlement history, including rejection outcomes. Unlike a
    successful-turn-only trace this retains repeated and aborted submissions. -/
def settleMany {Authorization : Type}
    (verifyAuthorization : Statement → Authorization → Bool)
    (compile : Statement → List Gate) :
    Ledger → List (Submission Authorization) → Ledger × List SettlementResult
  | ledger, [] => (ledger, [])
  | ledger, submission :: rest =>
    let next := settle verifyAuthorization compile ledger submission
    let tail := settleMany verifyAuthorization compile next.1 rest
    (tail.1, next.2 :: tail.2)

theorem settleMany_spent_monotone {Authorization : Type}
    (verifyAuthorization : Statement → Authorization → Bool)
    (compile : Statement → List Gate)
    (submissions : List (Submission Authorization))
    (ledger : Ledger) (n : BitVec 256) (hn : n ∈ ledger.spent) :
    n ∈ (settleMany verifyAuthorization compile ledger submissions).1.spent := by
  induction submissions generalizing ledger with
  | nil => exact hn
  | cons submission rest ih =>
    exact ih _ (settle_spent_monotone verifyAuthorization compile ledger submission n hn)

/-- Acceptance followed by any number of successful or rejected turns still
    rejects the same nullifier. Destination changes do not evade the spent set. -/
theorem accepted_nullifier_rejected_after_any_history {Authorization : Type}
    (verifyAuthorization : Statement → Authorization → Bool)
    (compile : Statement → List Gate)
    (ledger : Ledger) (first again : Submission Authorization)
    (rest : List (Submission Authorization))
    (hAccepted : (settle verifyAuthorization compile ledger first).2 = .accepted)
    (hSame : again.statement.nullifier = first.statement.nullifier) :
    let afterFirst := (settle verifyAuthorization compile ledger first).1
    let afterRest := (settleMany verifyAuthorization compile afterFirst rest).1
    settle verifyAuthorization compile afterRest again = (afterRest, .replay) := by
  intro afterFirst afterRest
  apply settle_replay_rejected
  rw [hSame]
  apply settleMany_spent_monotone
  have hInserted := settle_accept_inserts verifyAuthorization compile ledger first hAccepted
  change first.statement.nullifier ∈ (settle verifyAuthorization compile ledger first).1.spent
  rw [hInserted]
  exact .head _

/-- Guard-removal mutant: clearing the ledger before each attempt. -/
def settleWithoutReplayGuard {Authorization : Type}
    (verifyAuthorization : Statement → Authorization → Bool)
    (compile : Statement → List Gate)
    (_ledger : Ledger) (submission : Submission Authorization) : Ledger × SettlementResult :=
  settle verifyAuthorization compile ⟨[]⟩ submission

/-- Nonvacuity: a four-gate linked AND/XOR execution settles once. -/
def honestSubmission : Submission Unit where
  statement := ⟨[], 0#256, 7#256, 11#256, 0⟩
  authorization := ()
  witness := ⟨fun _ => 0xFFFFFFFFFFFFFFFF, fun _ => 0, fun _ => 0⟩

def honestCircuit (_ : Statement) : List Gate :=
  [.and 0 0 ⟨0xFFFFFFFFFFFFFFFF, 0, 0⟩,
   .xor 0 0,
   .and 0 0 ⟨0, 0, 0⟩,
   .xor 0 2]

private theorem honestSubmission_lanes_ok :
    shareUniformLanesCheck honestSubmission.witness = true := by
  unfold shareUniformLanesCheck honestSubmission
  apply (finAll_eq_true_iff 256 _).mpr
  intro _
  change (isUniformLaneWord 0xFFFFFFFFFFFFFFFF && isUniformLaneWord 0 && isUniformLaneWord 0) = true
  decide

private theorem honestSubmission_wires_zero :
    (witnessWires honestSubmission.witness)[0]? =
      some ⟨0xFFFFFFFFFFFFFFFF, 0, 0⟩ := by
  unfold witnessWires honestSubmission
  rw [List.getElem?_ofFn]
  simp only [Nat.zero_lt_succ, ↓reduceDIte]

private theorem honestSubmission_settle_eq :
    settle (fun (_ : Statement) (_ : Unit) => true) honestCircuit ⟨[]⟩ honestSubmission =
      (⟨[7#256]⟩, .accepted) := by
  let allOnes : RssWord64Shares3 := ⟨0xFFFFFFFFFFFFFFFF, 0, 0⟩
  have hNotMem : honestSubmission.statement.nullifier ∉ ([] : List (BitVec 256)) := by simp
  unfold settle
  rw [cIte_neg hNotMem]
  simp only [↓reduceIte]
  unfold run honestCircuit
  rw [honestSubmission_lanes_ok]
  simp only [↓reduceIte, evalGates, evalGate, honestSubmission_wires_zero]
  dsimp only [Bind.bind, Pure.pure, Option.bind]
  simp only [List.getElem?_cons_zero, List.getElem?_cons_succ]
  have hFin : finish ⟨allOnes :: ⟨0, 0, 0⟩ :: ⟨0, 0, 0⟩ :: allOnes :: witnessWires honestSubmission.witness,
      [⟨⟨0, 0, 0⟩, ⟨0, 0, 0⟩, ⟨0, 0, 0⟩⟩, ⟨allOnes, allOnes, allOnes⟩]⟩ = .accepted := by
    unfold finish PendingAnd.check RssWord64Shares3.reconstruct
    decide
  have hX1 : xorShares allOnes allOnes = ⟨0, 0, 0⟩ := by decide
  have hX2 : xorShares ⟨0, 0, 0⟩ allOnes = allOnes := by decide
  rw [hX1, hX2, hFin]
  rfl

theorem settlement_acceptance_witness :
    (settle (fun (_ : Statement) (_ : Unit) => true) honestCircuit ⟨[]⟩ honestSubmission).2 =
      .accepted := by
  rw [honestSubmission_settle_eq]

/-- Named reachability premise for structural nonvacuity registration. -/
def AcceptedSettlement {Authorization : Type}
    (verifyAuthorization : Statement → Authorization → Bool)
    (compile : Statement → List Gate) (ledger : Ledger)
    (submission : Submission Authorization) : Prop :=
  (settle verifyAuthorization compile ledger submission).2 = .accepted

theorem accepted_settlement_spends {Authorization : Type}
    (verifyAuthorization : Statement → Authorization → Bool)
    (compile : Statement → List Gate) (ledger : Ledger)
    (submission : Submission Authorization)
    (h : AcceptedSettlement verifyAuthorization compile ledger submission) :
    submission.statement.nullifier ∈
      (settle verifyAuthorization compile ledger submission).1.spent := by
  rw [settle_accept_inserts verifyAuthorization compile ledger submission h]
  exact .head _

theorem inhabited_accepted_settlement :
    ∃ ledger : Ledger, ∃ submission : Submission Unit,
      AcceptedSettlement (fun (_ : Statement) (_ : Unit) => true)
        honestCircuit ledger submission :=
  ⟨⟨[]⟩, honestSubmission, settlement_acceptance_witness⟩

set_option maxRecDepth 8192 in
/-- A statement-bound authorization witness, including destination and epoch.
    This models an authenticated statement token, not a cryptographic signature scheme. -/
theorem inhabited_statement_bound_settlement :
    ∃ ledger : Ledger, ∃ submission : Submission Statement,
      AcceptedSettlement (fun st authorization => decide (st = authorization))
        honestCircuit ledger submission := by
  refine ⟨⟨[]⟩, ⟨honestSubmission.statement, honestSubmission.statement, honestSubmission.witness⟩, ?_⟩
  simpa only [AcceptedSettlement, settle, decide_true, ↓reduceIte] using settlement_acceptance_witness

#verify_inhabited Qsag.MigrationExecution.accepted_settlement_spends
  Qsag.MigrationExecution.inhabited_statement_bound_settlement

/-- The same request is accepted twice only in the replay-guard mutant. -/
theorem tooth_replay_guard_removal :
    ∃ s : Submission Unit,
      let afterFirst := (settle (fun _ _ => true) honestCircuit ⟨[]⟩ s).1
      (settle (fun _ _ => true) honestCircuit afterFirst s).2 ≠
        (settleWithoutReplayGuard (fun _ _ => true) honestCircuit afterFirst s).2 := by
  refine ⟨honestSubmission, ?_⟩
  dsimp only
  have h1 : (settle (fun _ _ => true) honestCircuit ⟨[]⟩ honestSubmission).1 = ⟨[7#256]⟩ := by
    rw [honestSubmission_settle_eq]
  rw [h1,
      settle_replay_rejected (fun _ _ => true) honestCircuit ⟨[7#256]⟩ honestSubmission (.head _)]
  unfold settleWithoutReplayGuard
  rw [honestSubmission_settle_eq]
  decide

#tooth_pair Qsag.MigrationExecution.settle_replay_rejected vs
  Qsag.MigrationExecution.tooth_replay_guard_removal

#verify_constructive
  Qsag.MigrationExecution.rust_gf128_basis_kats
  Qsag.MigrationExecution.tooth_identity_basis_conversion_wrong
  Qsag.MigrationExecution.rustGf128Mul_comm
  Qsag.MigrationExecution.rustGf128Mul_assoc
  Qsag.MigrationExecution.towerToRust_mul
  Qsag.MigrationExecution.towerToRust_injective
  Qsag.MigrationExecution.towerToRust_rustToTower
  Qsag.MigrationExecution.rustToTower_towerToRust
  Qsag.MigrationExecution.rustToTower_mul
  Qsag.MigrationExecution.rustGf128Mul_eq_zero
  Qsag.MigrationExecution.foldRound_err
  Qsag.MigrationExecution.foldRound_false_claim_survives_at_most_two_coins
  Qsag.MigrationExecution.tooth_fold_message_after_coin_forges
  Qsag.MigrationExecution.baseAccepts_false_claim_at_most_two_coins
  Qsag.MigrationExecution.honest_fold_preserves_true_claim
  Qsag.MigrationExecution.honest_base_accepts
  Qsag.MigrationExecution.acceptingCoins_eq_filter
  Qsag.MigrationExecution.coinVectors_length
  Qsag.MigrationExecution.sacrificeBadCoinBound_closed
  Qsag.MigrationExecution.recursive_sacrifice_false_claim_accepting_coins_bound
  Qsag.MigrationExecution.tooth_sacrifice_without_product_test_accepts_false_claim
  Qsag.MigrationExecution.inhabited_sacrifice_accepted
  Qsag.MigrationExecution.checkBaseOpenings_sound
  Qsag.MigrationExecution.ownership_same_witness_or_joint_collision
  Qsag.MigrationExecution.finish_checks_consumed_outputs
  Qsag.MigrationExecution.run_checks_actual_lanes
  Qsag.MigrationExecution.run_has_checked_execution
  Qsag.MigrationExecution.accepted_execution_same_witness_in_every_lane
  Qsag.MigrationExecution.tooth_corrupt_final_and_guard_removal
  Qsag.MigrationExecution.settle_replay_rejected
  Qsag.MigrationExecution.settle_accept_inserts
  Qsag.MigrationExecution.settle_spent_monotone
  Qsag.MigrationExecution.settleMany_spent_monotone
  Qsag.MigrationExecution.accepted_nullifier_rejected_after_any_history
  Qsag.MigrationExecution.settlement_acceptance_witness
  Qsag.MigrationExecution.tooth_replay_guard_removal

end MigrationExecution

