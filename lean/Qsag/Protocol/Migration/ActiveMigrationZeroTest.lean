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
