module
/-
# Qsag.ActiveMigrationZeroTest — Canonical Curve Semantics, 3-Party 64-Lane RSS, `GF(2^128)` BBCGGI19 Sacrifice & `all_outputs_zero` / `InvalidTape` Privacy Barriers

Constructive (`0` choice axioms, `0` compiler-trust axioms) formalization, security
proofs, and explicit `#tooth` attack witnesses for the 3-custodian post-quantum migration ceremony
(`crates/qsag-migrate/src/{scalar.rs,secp256k1_ct.rs,legacy.rs,ownership.rs,co_zk_mpc.rs,outer_mpc.rs}`):

1. **Exact `SECP256K1_ORDER_N` & `ED25519_ORDER_L` Curve Subgroup Semantics + Pre-Migration Shor Boundary**:
   - Exact 256-bit subgroup orders (`SECP256K1_ORDER_N`, `ED25519_ORDER_L`), `ScalarGroup`, and
     circuit canonical range guard `requireCanonicalScalar` (`0 < s < group.orderNat`).
   - Non-injective Bitcoin Taproot `x`-only negation (`taprootXOnlySameX`, pairing `s` and
     `SECP_N - s` with `s ≠ SECP_N - s`), `#tooth` `tooth_taproot_xonly_not_injective_without_y_parity`
     refuting naive `Function.Injective pkOf`, and `taproot_even_y_parity_restores_canonical_injectivity`
     proving `y[0] == 0` (`ownership.rs:282`) restores canonical injectivity.
   - SLIP-0010 / RFC 8032 Ed25519 clamping (`clampEd25519Bytes32`) + `mod ED_ORDER` reduction
     (`normalizeSlip0010Ed25519Scalar`), proving every clamped digest reduces to a nonzero canonical
     scalar while wrapping non-injectively modulo `ED_ORDER` (`tooth_ed25519_clamped_wraps_mod_order_non_injective`).
   - Explicit Shor CRQC pre-migration boundary (`ShorVulnerablePreMigration` /
     `tooth_shor_crqc_breaks_legacy_pk_pre_migration`) paired with post-ceremony Poseidon2
     `NULLIFIER_DOMAIN` (`0x4d49_475f_4e55_4c31`) 11-limb binding & campaign replay resistance
     (`post_ceremony_nullifier_domain_binding_and_replay_sound`).

2. **Canonical `< group.orderNat` Premature-Open Key-Recovery `#tooth` (`canonicalSubgroupHom`)**:
   - Eliminates toy `Fin (2^w + 1)` groups in favor of `canonicalSubgroupHom (group : ScalarGroup)`
     over `Fin group.orderNat` (`Secp256k1` and `Ed25519`), proving both `non_two_torsion` across all
     256 bit generators (`odd_not_dvd_two_pow`) and strict injectivity on canonical scalars.
   - Proves `tooth_premature_residual_open_recovers_spending_key` (and its canonical instantiation
     `tooth_premature_residual_open_recovers_canonical_spending_key`): opening the public-key residual
     before `all_outputs_zero` lets 256 aborted 1-bit-fault queries recover 100% of `ks.secret`.

3. **3-Party 64-Lane Replicated Secret Sharing (`RssBit64`) & `shareUniformLanesCheck`**:
   - Models 3-custodian 64-lane RSS (`party i` holds `(w_i, w_{i+1})`) and `shareUniformLanesCheck`
     enforcing `0` or `0xFFFFFFFFFFFFFFFF` per witness bit word (`co_zk_mpc.rs:126-131`), paired
     with `tooth_non_uniform_lanes_split_witness_across_reps`.

4. **Algebraic `GF(2^128)` (`Tower128`) BBCGGI19 Sacrifice & Coin-Permuted Triple Bucketing**:
   - Models `verifyAllPendingGf2128` over `Tower128 := TowerElem 7` and proves via
     `RoundPoly.roots_nodup_length_le` + `towerNoZeroDivisors 7` that any nonzero multiplication
     fault passes on at most `m` challenges out of any `Nodup` challenge set `S : List Tower128`
     (`≤ m / 2^128`), paired with `tooth_unverified_mul_forges_all_outputs_zero`.
   - Replaces Boolean sacrifice flags with authentic `Tower128` OT correlation checks
     (`otSacrificeCheckGf2128`) for `coin_permuted_bucketing_hides_wire_and_bounds_double_fault`
     vs. `tooth_fixed_bucket_selective_abort_leaks_wire_bit`.

5. **`verify_all_pending` -> `all_outputs_zero` -> `PRECOMMIT` -> `FREEZE` Barrier, `InvalidTape` Conditional-Privacy Analysis & Multi-Turn `compose_forward_sim` Spine**:
   - Proves via `mask_bijection_hop` that corrupt custodian `0`'s joint abort view (RSS replica
     `(s0', s1')` missing `s2'` + upfront `validTape` + masked `Tower128` BBCGGI19 base-case
     openings `(alpha, beta, gamma)` + `openedAllOutputsZero = false`) leaks `0` bits of `ks.secret`.
   - Formalizes the upfront `Error::InvalidTape` (`co_zk_mpc.rs:743-750`) conditional-privacy
     boundary (`upfront_invalid_tape_independent_of_spending_key`) vs. `#tooth`
     `tooth_premature_witness_range_in_invalid_tape_leaks_secret_bit`.
   - Lifts the 3-party RSS + `InvalidTape` + BBCGGI19 + `allOutputsZero` custodian state machine
     across unbounded multi-turn traces via `compose_forward_sim` (`multi_turn_hardened_ceremony_trace_safe`).
-/

public import Qsag.Constructive
public import Qsag.BinaryTower
public import Qsag.SimulationSpine
public import Qsag.UcGames
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

/-- Abstract curve `x`-only & `y`-LSB parity projection on `secp256k1` (`ownership.rs:281-284`):
    `[s]G` and `[SECP_N - s]G` share the exact same `x`-coordinate (`sameX_iff`) and have
    opposite `y[0]` parity over the odd base prime `SECP_P` (`yParity_neg`). -/
structure TaprootCurveProjection (XCoord : Type) where
  xOf         : BitVec 256 → XCoord
  yParity     : BitVec 256 → Bool
  sameX_iff   : ∀ s1 s2,
    requireCanonicalScalar .Secp256k1 s1 = true →
    requireCanonicalScalar .Secp256k1 s2 = true →
    (xOf s1 = xOf s2 ↔ taprootXOnlySameX s1 s2)
  yParity_neg : ∀ s,
    requireCanonicalScalar .Secp256k1 s = true →
    yParity (secpNegScalar s) = !(yParity s)

/-- Constructive model of `TaprootCurveProjection` on `BitVec 256` witnessing inhabitedness. -/
def canonicalTaprootProjection : TaprootCurveProjection (BitVec 256) where
  xOf s :=
    if requireCanonicalScalar .Secp256k1 s then
      BitVec.ofNat 256 (if s.toNat ≤ SECP256K1_ORDER_N - s.toNat then s.toNat else SECP256K1_ORDER_N - s.toNat)
    else
      0#256
  yParity s := decide (SECP256K1_ORDER_N < 2 * s.toNat)
  sameX_iff s1 s2 h1 h2 := by
    have hb := curve_orders_match_le_limbs_and_bounds
    obtain ⟨hp1, hl1⟩ := (requireCanonicalScalar_iff .Secp256k1 s1).mp h1
    obtain ⟨hp2, hl2⟩ := (requireCanonicalScalar_iff .Secp256k1 s2).mp h2
    dsimp only [ScalarGroup.orderNat] at hl1 hl2
    rw [h1, h2]
    simp only [↓reduceIte]
    let m1 := if s1.toNat ≤ SECP256K1_ORDER_N - s1.toNat then s1.toNat else SECP256K1_ORDER_N - s1.toNat
    let m2 := if s2.toNat ≤ SECP256K1_ORDER_N - s2.toNat then s2.toNat else SECP256K1_ORDER_N - s2.toNat
    have hm1Lt : m1 < 2 ^ 256 := by dsimp [m1]; split <;> omega
    have hm2Lt : m2 < 2 ^ 256 := by dsimp [m2]; split <;> omega
    constructor
    · intro hEq
      have hv := congrArg BitVec.toNat hEq
      rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm1Lt, Nat.mod_eq_of_lt hm2Lt] at hv
      refine ⟨h1, h2, ?_⟩
      dsimp [m1, m2] at hv
      cases (inferInstance : Decidable (s1.toNat ≤ SECP256K1_ORDER_N - s1.toNat)) with
      | isTrue ha =>
        rw [cIte_pos ha] at hv
        cases (inferInstance : Decidable (s2.toNat ≤ SECP256K1_ORDER_N - s2.toNat)) with
        | isTrue hc =>
          rw [cIte_pos hc] at hv
          exact Or.inl (BitVec.eq_of_toNat_eq hv)
        | isFalse hc =>
          rw [cIte_neg hc] at hv
          exact Or.inr (by omega)
      | isFalse ha =>
        rw [cIte_neg ha] at hv
        cases (inferInstance : Decidable (s2.toNat ≤ SECP256K1_ORDER_N - s2.toNat)) with
        | isTrue hc =>
          rw [cIte_pos hc] at hv
          exact Or.inr (by omega)
        | isFalse hc =>
          rw [cIte_neg hc] at hv
          exact Or.inl (BitVec.eq_of_toNat_eq (by omega))
    · rintro ⟨_, _, hOr⟩
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm1Lt, Nat.mod_eq_of_lt hm2Lt]
      dsimp [m1, m2]
      rcases hOr with rfl | hNeg
      · rfl
      · cases (inferInstance : Decidable (s1.toNat ≤ SECP256K1_ORDER_N - s1.toNat)) with
        | isTrue ha =>
          rw [cIte_pos ha]
          cases (inferInstance : Decidable (s2.toNat ≤ SECP256K1_ORDER_N - s2.toNat)) with
          | isTrue hc => rw [cIte_pos hc]; omega
          | isFalse hc => rw [cIte_neg hc]; omega
        | isFalse ha =>
          rw [cIte_neg ha]
          cases (inferInstance : Decidable (s2.toNat ≤ SECP256K1_ORDER_N - s2.toNat)) with
          | isTrue hc => rw [cIte_pos hc]; omega
          | isFalse hc => rw [cIte_neg hc]; omega
  yParity_neg s hCanon := by
    have hb := curve_orders_match_le_limbs_and_bounds
    have hOdd : SECP256K1_ORDER_N % 2 = 1 := hb.2.2.2.2.1
    obtain ⟨hNegToNat, _, _, _, _⟩ := secpNegScalar_props hCanon
    obtain ⟨hPos, hLtN⟩ := (requireCanonicalScalar_iff .Secp256k1 s).mp hCanon
    dsimp only [ScalarGroup.orderNat] at hLtN
    rw [hNegToNat]
    cases (inferInstance : Decidable (SECP256K1_ORDER_N < 2 * s.toNat)) with
    | isTrue hGt =>
      have hNot : ¬ (SECP256K1_ORDER_N < 2 * (SECP256K1_ORDER_N - s.toNat)) := by omega
      rw [decide_eq_true hGt, decide_eq_false hNot]
      rfl
    | isFalse hLe =>
      have hYes : SECP256K1_ORDER_N < 2 * (SECP256K1_ORDER_N - s.toNat) := by omega
      rw [decide_eq_false hLe, decide_eq_true hYes]
      rfl

/-- **`#tooth` Taproot `x`-Only Non-Injectivity Without `y[0]` Parity (`tooth_taproot_xonly_not_injective_without_y_parity`)**:
    Without `ownership.rs:282` (`c.output(y[0])`), `proj.xOf` is **never** injective — not even on
    canonical nonzero scalars `[1, SECP_N - 1]`, because `1#256` and `secpNegScalar 1#256` are
    distinct canonical scalars sharing the identical `x`-coordinate! -/
theorem tooth_taproot_xonly_not_injective_without_y_parity
    {XCoord : Type} (proj : TaprootCurveProjection XCoord) :
    ¬ Function.Injective proj.xOf ∧
    (let s1 : BitVec 256 := 1#256
     let s2 : BitVec 256 := secpNegScalar s1
     requireCanonicalScalar .Secp256k1 s1 = true ∧
     requireCanonicalScalar .Secp256k1 s2 = true ∧
     s1 ≠ s2 ∧
     taprootXOnlySameX s1 s2 ∧
     proj.xOf s1 = proj.xOf s2) := by
  have h1Canon : requireCanonicalScalar .Secp256k1 1#256 = true := by
    unfold requireCanonicalScalar ScalarGroup.orderNat SECP256K1_ORDER_N
    decide
  obtain ⟨_, h2Canon, _, hNe, hSameX⟩ := secpNegScalar_props h1Canon
  have hXEq : proj.xOf 1#256 = proj.xOf (secpNegScalar 1#256) :=
    (proj.sameX_iff 1#256 (secpNegScalar 1#256) h1Canon h2Canon).mpr hSameX
  refine ⟨fun hInj => hNe (hInj hXEq), h1Canon, h2Canon, hNe, hSameX, hXEq⟩

/-- Normalize any canonical `secp256k1` scalar to its even-`y` Taproot representative (`legacy.rs:299-301, 319-321`). -/
def normalizeTaprootEvenY {XCoord : Type} (proj : TaprootCurveProjection XCoord)
    (s : BitVec 256) : BitVec 256 :=
  if proj.yParity s then secpNegScalar s else s

/-- **Taproot Even-`y` Parity Constraint Restores Canonical Injectivity (`taproot_even_y_parity_restores_canonical_injectivity`)**:
    1. Enforcing `proj.yParity s = false` (`c.output(y[0])` at `ownership.rs:282`) makes `proj.xOf`
       strictly injective across all canonical `secp256k1` scalars.
    2. Compressed `(proj.xOf s, proj.yParity s)` (`BitcoinHash160` at `ownership.rs:265-267`) is
       strictly injective across **all** canonical scalars `1 ≤ s < SECP_N`.
    3. `normalizeTaprootEvenY` produces a canonical scalar sharing the same `x`-coordinate with
       guaranteed even `y[0]` parity (`false`). -/
theorem taproot_even_y_parity_restores_canonical_injectivity
    {XCoord : Type} (proj : TaprootCurveProjection XCoord) :
    (∀ s1 s2 : BitVec 256,
      requireCanonicalScalar .Secp256k1 s1 = true →
      requireCanonicalScalar .Secp256k1 s2 = true →
      proj.yParity s1 = false →
      proj.yParity s2 = false →
      proj.xOf s1 = proj.xOf s2 →
      s1 = s2) ∧
    (∀ s1 s2 : BitVec 256,
      requireCanonicalScalar .Secp256k1 s1 = true →
      requireCanonicalScalar .Secp256k1 s2 = true →
      proj.xOf s1 = proj.xOf s2 →
      proj.yParity s1 = proj.yParity s2 →
      s1 = s2) ∧
    (∀ s : BitVec 256,
      requireCanonicalScalar .Secp256k1 s = true →
      requireCanonicalScalar .Secp256k1 (normalizeTaprootEvenY proj s) = true ∧
      proj.xOf (normalizeTaprootEvenY proj s) = proj.xOf s ∧
      proj.yParity (normalizeTaprootEvenY proj s) = false) := by
  have hPairInj : ∀ s1 s2 : BitVec 256,
      requireCanonicalScalar .Secp256k1 s1 = true →
      requireCanonicalScalar .Secp256k1 s2 = true →
      proj.xOf s1 = proj.xOf s2 →
      proj.yParity s1 = proj.yParity s2 →
      s1 = s2 := by
    intro s1 s2 h1 h2 hX hY
    have hSame := (proj.sameX_iff s1 s2 h1 h2).mp hX
    rcases hSame.2.2 with hEq | hNegNat
    · exact hEq
    · obtain ⟨hNegToNat, _, _, _, _⟩ := secpNegScalar_props h1
      have hs2EqNeg : s2 = secpNegScalar s1 :=
        BitVec.eq_of_toNat_eq (hNegNat.trans hNegToNat.symm)
      subst hs2EqNeg
      have hFlip := proj.yParity_neg s1 h1
      rw [hFlip] at hY
      cases hb : proj.yParity s1 <;> rw [hb] at hY <;> cases hY
  refine ⟨fun s1 s2 h1 h2 hy1 hy2 hX => hPairInj s1 s2 h1 h2 hX (hy1.trans hy2.symm), hPairInj, ?_⟩
  intro s hCanon
  unfold normalizeTaprootEvenY
  cases hy : proj.yParity s
  · change requireCanonicalScalar .Secp256k1 s = true ∧ proj.xOf s = proj.xOf s ∧ proj.yParity s = false
    exact ⟨hCanon, rfl, hy⟩
  · change requireCanonicalScalar .Secp256k1 (secpNegScalar s) = true ∧
      proj.xOf (secpNegScalar s) = proj.xOf s ∧
      proj.yParity (secpNegScalar s) = false
    obtain ⟨_, hNegCanon, _, _, hSame⟩ := secpNegScalar_props hCanon
    have hXEq : proj.xOf s = proj.xOf (secpNegScalar s) :=
      (proj.sameX_iff s (secpNegScalar s) hCanon hNegCanon).mpr hSame
    have hNegPar := proj.yParity_neg s hCanon
    rw [hy] at hNegPar
    exact ⟨hNegCanon, hXEq.symm, hNegPar⟩

#tooth_pair
  Qsag.taproot_even_y_parity_restores_canonical_injectivity
  vs
  Qsag.tooth_taproot_xonly_not_injective_without_y_parity

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
    (∀ raw : BitVec 256,
      ED25519_ORDER_L < (clampEd25519Bytes32 raw).toNat ∧
      requireCanonicalScalar .Ed25519 (clampEd25519Bytes32 raw) = false ∧
      reduceEd25519Order (clampEd25519Bytes32 raw) ≠ clampEd25519Bytes32 raw) ∧
    (let x1 : BitVec 256 := clampEd25519Bytes32 0#256
     let x2 : BitVec 256 := BitVec.ofNat 256 (x1.toNat - ED25519_ORDER_L)
     ED25519_ORDER_L ≤ x1.toNat ∧
     ED25519_ORDER_L ≤ x2.toNat ∧
     x1 ≠ x2 ∧
     reduceEd25519Order x1 = reduceEd25519Order x2) ∧
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
  refine ⟨hAllWrap, ⟨hx1Ge, hx2Ge, hx1NeX2, hRedEq⟩,
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

private theorem modAddVal_assoc {M a b c : Nat} (ha : a < M) (_hb : b < M) (hc : c < M) :
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

private theorem modSub_modAdd_cancel {M a b : Nat} (ha : a < M) (_hb : b < M) :
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
    (hOdd : M % 2 = 1) (_hp : p < M) (hgLt : g < M) (hgPos : 0 < g) :
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

/-- Authentic cyclic subgroup homomorphism `Fin group.orderNat` for `Secp256k1` (`SECP_N`) and
    `Ed25519` (`ED_ORDER`), modeling parity-pinned / compressed curve points `[s mod order]G`. -/
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
  add_assoc a b c := Fin.ext (modAddVal_assoc a.isLt b.isLt c.isLt)
  zero_add a := Fin.ext (modAddVal_zero_left a.isLt)
  add_sub_cancel a b := Fin.ext (modSub_modAdd_cancel a.isLt b.isLt)
  sub_add_cancel a b := Fin.ext (modAdd_modSub_cancel a.isLt b.isLt)
  non_two_torsion i _hi p := by
    intro hEq
    have hValEq := congrArg Fin.val hEq
    dsimp only at hValEq
    obtain ⟨hGt1, _, hOdd⟩ := scalarGroup_order_props group
    have hgNe0 : (2 ^ i) % group.orderNat ≠ 0 := odd_not_dvd_two_pow hOdd hGt1 i
    have hgLt : (2 ^ i) % group.orderNat < group.orderNat := Nat.mod_lt _ (by omega)
    exact modAdd_ne_modSub_of_odd hOdd p.isLt hgLt (Nat.pos_of_ne_zero hgNe0) hValEq
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
