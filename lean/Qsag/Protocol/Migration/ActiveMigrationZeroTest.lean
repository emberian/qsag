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
degree-30 round 0 of the `D0_BITS = 16` packing, numerator `54`) are proved in §11 below.
The packing of the current `outer_mpc.rs` (`BIT_CHECK_NUMERATOR = 63`: seven weight
challenges, six ternary sumcheck rounds, eighteen halving rounds) is counted in §11A by
`staged_sacrifice_false_claim_accepting_coins_bound` and `rust_bit_check_numerator_63_bound`,
and the thirteen stages ahead of the halving rounds are discharged unconditionally in §11B
by `rustBitCheckStages_sound` and `rust_bit_check_63_concrete_accepting_coins_bound`.
-/

public import Qsag.Tactic.Prelude
public import Qsag.Math.Gf2Pow128
public import Qsag.Spec.Refines
public import Qsag.Protocol.Aggregation.UcGames
public import Qsag.Tactic.AssuranceKit
public import Qsag.Math.Tactic.MaskBijection

public import Qsag.Math.EllipticCurves

public section

namespace Qsag

-- `Fin.instLinearOrderPackage` supplies a `BEq (Fin n)` whose package proofs use `Classical.choice`;
-- without it `==` on `Fin` resolves to `instBEqOfDecidableEq`.
attribute [-instance] Fin.instLinearOrderPackage

set_option autoImplicit false

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

open MigrationExecution in
private theorem bxor_left_comm (a b c : RustGf128) : a ^^^ (b ^^^ c) = b ^^^ (a ^^^ c) := by
  rw [← BitVec.xor_assoc, BitVec.xor_comm a b, BitVec.xor_assoc]

open MigrationExecution in
private theorem bxor_cancel (a b : RustGf128) : a ^^^ (a ^^^ b) = b := by
  rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

private theorem ite_twoPow_bit (c : Bool) (j i : Nat) (hj : j < 128) :
    (if c then BitVec.twoPow 128 j else 0#128).getLsbD i = (c && decide (j = i)) := by
  cases c
  · exact BitVec.getLsbD_zero
  · rw [cIte_pos rfl, BitVec.getLsbD_twoPow, decide_eq_true hj]

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
  refine ⟨NULLIFIER_DOMAIN_eq, ?_, fun _ _ _ _ _ _ => rfl⟩
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
        have hTag := congrArg (fun f => f ⟨0, by decide⟩) hFunEq
        dsimp only [migrationNullifierInput] at hTag
        exact ScalarGroup.nullifierTag_injective hTag
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
      have hTag := congrArg (fun f => f ⟨0, by decide⟩) hSameIn
      dsimp only [migrationNullifierInput] at hTag
      exact ScalarGroup.nullifierTag_injective hTag
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
    qsum 4 (fun i =>
      if fixedBucketDoubleFaultSurvivesGf2128 chi u0L aL deltaL u0R aR deltaR (boolPairSampleEnum.toFun i)
      then 1 else 0) = 1 := by
  have hCongr :
      qsum 4 (fun i =>
        if fixedBucketDoubleFaultSurvivesGf2128 chi u0L aL deltaL u0R aR deltaR (boolPairSampleEnum.toFun i)
        then 1 else 0) =
      qsum 4 (fun i => if i = (⟨0, by decide⟩ : Fin 4) then 1 else 0) := by
    apply qsum_congr
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
  rw [hCongr, qsum_eq_indicator]

/-- **`#tooth` Fixed-Bucket `k + 2N` Selective-Abort Wire-Bit Leak Over `Tower128` (`tooth_fixed_bucket_selective_abort_leaks_wire_bit`)**:
    Under deterministic `(k, k + 2N)` combine without post-lock coin permutation, injecting nonzero
    `Tower128` OT faults `deltaL, deltaR ≠ 0` passes both algebraic `GF(2^128)` sacrifice checks in
    exact `1 / 4` of sessions (`qsum 4 = 1`) and reveals the honest online wire bit `y` with
    probability `1`! -/
theorem tooth_fixed_bucket_selective_abort_leaks_wire_bit
    {chi u0L aL deltaL u0R aR deltaR : Tower128}
    (hChi : chi ≠ towerZero 7) (hDL : deltaL ≠ towerZero 7) (hDR : deltaR ≠ towerZero 7) :
    ∃ survivalCount : Nat,
      survivalCount = qsum 4 (fun i =>
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
  let survivalCount := qsum 4 (fun i =>
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

private theorem qsum_unique_bool_le_one (k : Nat) (p : Fin k → Bool)
    (hUnique : ∀ a b : Fin k, p a = true → p b = true → a = b) :
    qsum k (fun c => if p c then 1 else 0) ≤ 1 := by
  have hSpec := finFind?_spec k p
  cases hFind : finFind? k p with
  | none =>
    rw [hFind] at hSpec
    dsimp only at hSpec
    have hCongr : qsum k (fun c => if p c then 1 else 0) = qsum k (fun _ => 0) := by
      apply qsum_congr
      intro c
      rw [hSpec c]
      rfl
    rw [hCongr, qsum_const]
    omega
  | some c₀ =>
    rw [hFind] at hSpec
    dsimp only at hSpec
    have hCongr : qsum k (fun c => if p c then 1 else 0) =
        qsum k (fun c => if c = c₀ then 1 else 0) := by
      apply qsum_congr
      intro c
      cases hpc : p c
      · have hcNe : c ≠ c₀ := fun hEq => by subst hEq; rw [hpc] at hSpec; cases hSpec
        rw [cIte_neg hcNe]
        rfl
      · have hcEq : c = c₀ := hUnique c c₀ hpc hSpec
        rw [cIte_pos hcEq]
        rfl
    rw [hCongr, qsum_eq_indicator]
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
      qsum 2 (fun idx =>
        weight (onlineBeaverOpenBit y (combineBucketBit bLeft (boolSampleEnum.toFun idx)))) =
      qsum 2 (fun idx =>
        weight (boolSampleEnum.toFun idx))) ∧
    (let partnerHitCount := qsum (2 * N - 1) (fun c => if partnerOfI0 c == i1 then 1 else 0)
     let jointBadOutcomes := qsum 4 (fun s =>
       qsum (2 * N - 1) (fun c =>
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
      qsum_unique_bool_le_one (2 * N - 1) (fun c => partnerOfI0 c == i1)
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
        jointBadOutcomes ≤ qsum 4 (fun s => if s = (⟨0, by decide⟩ : Fin 4) then 1 else 0) := by
      apply qsum_le_qsum
      intro s
      if hs0 : s = ⟨0, by decide⟩ then
        subst hs0
        have hTrue : fixedBucketDoubleFaultSurvivesGf2128 chi u0L aL deltaL u0R aR deltaR
            (boolPairSampleEnum.toFun ⟨0, by decide⟩) = true := by
          rw [@fixedBucketDoubleFaultSurvivesGf2128_eq_both_false chi u0L aL deltaL u0R aR deltaR hChi hDL hDR]
          decide
        rw [cIte_pos rfl]
        have hEqHit : qsum (2 * N - 1) (fun c =>
            if fixedBucketDoubleFaultSurvivesGf2128 chi u0L aL deltaL u0R aR deltaR
                (boolPairSampleEnum.toFun ⟨0, by decide⟩) && (partnerOfI0 c == i1)
            then 1 else 0) = partnerHitCount := by
          apply qsum_congr
          intro c
          rw [hTrue, Bool.true_and]
        rw [hEqHit]
        exact hHitLe
      else
        have hFalse := hSurvFalseAt s hs0
        rw [cIte_neg hs0]
        have hZero : qsum (2 * N - 1) (fun c =>
            if fixedBucketDoubleFaultSurvivesGf2128 chi u0L aL deltaL u0R aR deltaR
                (boolPairSampleEnum.toFun s) && (partnerOfI0 c == i1)
            then 1 else 0) = qsum (2 * N - 1) (fun _ => 0) := by
          apply qsum_congr
          intro c
          rw [hFalse, Bool.false_and]
          rfl
        rw [hZero, qsum_const]
        omega
    rw [qsum_eq_indicator] at hJointLeInd
    have hDenPos : 0 < 4 * (2 * N - 1) := by omega
    exact ⟨hHitLe, hJointLeInd, ⟨hDenPos, hDenPos, Nat.mul_le_mul_right _ hJointLeInd⟩⟩

#tooth_pair
  Qsag.coin_permuted_bucketing_hides_wire_and_bounds_double_fault
  vs
  Qsag.tooth_fixed_bucket_selective_abort_leaks_wire_bit

/-! ## 6. `verify_all_pending` -> `all_outputs_zero` -> `PRECOMMIT` -> `FREEZE` Barrier, `InvalidTape` Conditional-Privacy -/

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
    qsum C (fun i =>
      weight (realHardenedRssCeremonyView group drawValidPred zkCommit ks delta
        seed0 seed1 seed2 aFin bFin rb (enum.toFun i))) =
    qsum C (fun i =>
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
  apply qsum_bijection_hop_eq enum padEquiv
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

private theorem natAbsDiff_qsum_indicator_self {C : Nat} (p : Fin C → Bool) :
    natAbsDiff (qsum C (fun i => if p i then 1 else 0))
               (qsum C (fun i => if p i then 1 else 0)) = 0 := by
  have hLe := qsum_indicator_diff_le p p (fun _ => false) (fun _ _ => rfl)
  simp only [Bool.false_eq_true, ↓reduceIte, qsum_const, Nat.mul_zero] at hLe
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
      (qsum C (fun i =>
        if D (realHardenedRssCeremonyView group drawValidPred zkCommit ksA delta
          seed0 seed1 seed2 aFinA bFinA rb (enum.toFun i))
        then 1 else 0))
      (qsum C (fun i =>
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
  exact natAbsDiff_qsum_indicator_self _

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
      qsum Cs (fun i =>
        weightBool (evalUpfrontTapeValidity drawValidPred seed0' seed1 (enumSeed.toFun i))) =
      qsum Cs (fun i =>
        weightBool (drawValidPred (enumSeed.toFun i)))) ∧
    (∀ (ksA ksB : RssKeyShares3) (delta seed2 : MigrationKey256)
       (aFinA bFinA aFinB bFinB rb : Tower128)
       (D : HardenedRssCeremonyView ZkView → Bool),
      ksA.s0 = ksB.s0 →
      evalUpfrontTapeValidity drawValidPred seed0' seed1 seed2 = false →
      natAbsDiff
        (qsum C (fun i =>
          if D (realHardenedRssCeremonyView group drawValidPred zkCommit ksA delta
            seed0' seed1 seed2 aFinA bFinA rb (enumPads.toFun i))
          then 1 else 0))
        (qsum C (fun i =>
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
        qsum C (fun i =>
          wFn (realHardenedRssCeremonyView group drawValidPred zkCommit ksA delta
            seed0' seed1 seed2 aFinA bFinA rb (enumPads.toFun i))) =
        qsum C (fun i =>
          wFn (simHardenedAbortView ZkView (ksA.s0 ^^^ delta) false (enumPads.toFun i))) := by
      unfold realHardenedRssCeremonyView simHardenedAbortView
      simp only [hInvalid, Bool.not_false, ↓reduceIte]
      mask_bijection_hop (SimpleEquiv.prodCongr (bvXorEquiv ksA.s1) (SimpleEquiv.refl _))
    have hSimB :
        qsum C (fun i =>
          wFn (realHardenedRssCeremonyView group drawValidPred zkCommit ksB delta
            seed0' seed1 seed2 aFinB bFinB rb (enumPads.toFun i))) =
        qsum C (fun i =>
          wFn (simHardenedAbortView ZkView (ksB.s0 ^^^ delta) false (enumPads.toFun i))) := by
      unfold realHardenedRssCeremonyView simHardenedAbortView
      simp only [hInvalid, Bool.not_false, ↓reduceIte]
      mask_bijection_hop (SimpleEquiv.prodCongr (bvXorEquiv ksB.s1) (SimpleEquiv.refl _))
    dsimp only [wFn] at hSimA hSimB
    rw [hSimA, hSimB, hSameS0]
    exact natAbsDiff_qsum_indicator_self _

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

/-! ## 7. Multi-Turn 3-Party RSS + BBCGGI19 + `all_outputs_zero` State Machine & Refinement to the Ideal Zero-Fault Machine (`Spec.Refines`) -/

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
    Spec.Machine ConcreteCustodianState RssCeremonyTurnInput ZkView where
  Init st := requireCanonicalScalar st.group st.shares.secret = true
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

/-- Layer 2: Intermediate barrier-gate `Spec.Machine` operating over `st.secret ^^^ inp.deltaScalar`. -/
def residualGateMachine {ZkView : Type}
    (drawValidPred : MigrationKey256 → Bool)
    (zkCommit : MigrationKey256 → ZkView) :
    Spec.Machine AbstractCustodianState RssCeremonyTurnInput ZkView where
  Init st := requireCanonicalScalar st.group st.secret = true
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
    Spec.Machine AbstractCustodianState RssCeremonyTurnInput ZkView where
  Init st := requireCanonicalScalar st.group st.secret = true
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
    Spec.LockstepSim
      (concreteCustodianMachine drawValidPred zkCommit)
      (residualGateMachine drawValidPred zkCommit) where
  Inv _ := True
  abs st :=
    { group := st.group
      secret := st.shares.secret
      completed := st.completed
      aborted := st.aborted }
  init_inv hInit := ⟨trivial, hInit⟩
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

/-- Forward refinement from Layer 2 (`residualGateMachine`) to Layer 3 (`idealZeroFaultMachine`),
    preserving `requireCanonicalScalar st.group st.secret = true` across every transition. -/
def residualGate_to_ideal_refines {ZkView : Type}
    (drawValidPred : MigrationKey256 → Bool)
    (zkCommit : MigrationKey256 → ZkView) :
    Spec.Refines
      (residualGateMachine drawValidPred zkCommit)
      (idealZeroFaultMachine drawValidPred zkCommit) where
  Rel s₁ s₂ := s₁ = s₂ ∧ requireCanonicalScalar s₁.group s₁.secret = true
  absInit s := s
  init_ok hInit := ⟨hInit, rfl, hInit⟩
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

/-- End-to-end 3-layer refinement: the lockstep link composed with the Layer 2 to Layer 3
    refinement by `Spec.Refines.trans`. -/
def custodian_to_ideal_spine {ZkView : Type}
    (drawValidPred : MigrationKey256 → Bool)
    (zkCommit : MigrationKey256 → ZkView) :
    Spec.Refines
      (concreteCustodianMachine drawValidPred zkCommit)
      (idealZeroFaultMachine drawValidPred zkCommit) :=
  (custodian_to_residualGate_lockstep drawValidPred zkCommit).toRefines.trans
    (residualGate_to_ideal_refines drawValidPred zkCommit)

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
  have hRel₀ : (custodian_to_ideal_spine drawValidPred zkCommit).Rel
      ⟨group, ks, comp₀, abort₀⟩ ⟨group, ks.secret, comp₀, abort₀⟩ := by
    unfold custodian_to_ideal_spine
    rw [Spec.Refines.trans_rel]
    exact ⟨⟨group, ks.secret, comp₀, abort₀⟩,
      (Spec.LockstepSim.toRefines_rel _ _ _).mpr ⟨trivial, rfl⟩, ⟨rfl, hCanon⟩⟩
  obtain ⟨_, hIdeal, _⟩ :=
    (custodian_to_ideal_spine drawValidPred zkCommit).lift_validTrace hRel₀ hTrace
  refine ⟨idealZeroFault_trace_inv drawValidPred zkCommit hIdeal, ?_⟩
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

/-- Settlement accepts exactly when the nullifier is fresh, the authorization
    verifies against the full statement, and the compiled circuit run accepts. -/
theorem settle_accepted_iff {Authorization : Type}
    (verifyAuthorization : Statement → Authorization → Bool)
    (compile : Statement → List Gate)
    (ledger : Ledger) (submission : Submission Authorization) :
    (settle verifyAuthorization compile ledger submission).2 = .accepted ↔
      (¬ (submission.statement.nullifier ∈ ledger.spent) ∧
        verifyAuthorization submission.statement submission.authorization = true ∧
        run submission.witness (compile submission.statement) = .accepted) := by
  constructor
  · intro h
    unfold settle at h
    cases (inferInstance : Decidable (submission.statement.nullifier ∈ ledger.spent)) with
    | isTrue hMem =>
      rw [cIte_pos hMem] at h
      cases h
    | isFalse hMem =>
      rw [cIte_neg hMem] at h
      cases hAuth : verifyAuthorization submission.statement submission.authorization
      · simp only [hAuth, Bool.false_eq_true, ↓reduceIte] at h
        cases h
      · simp only [hAuth, ↓reduceIte] at h
        cases hr : run submission.witness (compile submission.statement)
        case accepted => exact ⟨hMem, rfl, rfl⟩
        all_goals (simp only [hr] at h <;> cases h)
  · intro h
    obtain ⟨hMem, hAuth, hRun⟩ := h
    unfold settle
    rw [cIte_neg hMem]
    simp only [hAuth, ↓reduceIte, hRun]

/-- Every non-accepting outcome (replay, bad authorization, rejected run)
    leaves the ledger untouched. -/
theorem settle_reject_ledger_unchanged {Authorization : Type}
    (verifyAuthorization : Statement → Authorization → Bool)
    (compile : Statement → List Gate)
    (ledger : Ledger) (submission : Submission Authorization)
    (h : ¬ ((settle verifyAuthorization compile ledger submission).2 = .accepted)) :
    (settle verifyAuthorization compile ledger submission).1 = ledger := by
  cases (inferInstance : Decidable (submission.statement.nullifier ∈ ledger.spent)) with
  | isTrue hMem =>
    rw [settle_replay_rejected verifyAuthorization compile ledger submission hMem]
  | isFalse hMem =>
    cases hAuth : verifyAuthorization submission.statement submission.authorization
    · unfold settle
      rw [cIte_neg hMem]
      simp only [hAuth, Bool.false_eq_true, ↓reduceIte]
    · cases hr : run submission.witness (compile submission.statement)
      case accepted =>
        exact absurd ((settle_accepted_iff verifyAuthorization compile ledger submission).2
          ⟨hMem, hAuth, hr⟩) h
      all_goals
        unfold settle
        rw [cIte_neg hMem]
        simp only [hAuth, ↓reduceIte, hr]

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
  Qsag.MigrationExecution.foldRound_err
  Qsag.MigrationExecution.foldRound_false_claim_survives_at_most_two_coins
  Qsag.MigrationExecution.baseAccepts_false_claim_at_most_two_coins
  Qsag.MigrationExecution.honest_fold_preserves_true_claim
  Qsag.MigrationExecution.honest_base_accepts
  Qsag.MigrationExecution.acceptingCoins_eq_filter
  Qsag.MigrationExecution.coinVectors_length
  Qsag.MigrationExecution.sacrificeBadCoinBound_closed
  Qsag.MigrationExecution.recursive_sacrifice_false_claim_accepting_coins_bound
  Qsag.MigrationExecution.checkBaseOpenings_sound
  Qsag.MigrationExecution.ownership_same_witness_or_joint_collision
  Qsag.MigrationExecution.finish_checks_consumed_outputs
  Qsag.MigrationExecution.run_checks_actual_lanes
  Qsag.MigrationExecution.run_has_checked_execution
  Qsag.MigrationExecution.accepted_execution_same_witness_in_every_lane
  Qsag.MigrationExecution.tooth_corrupt_final_and_guard_removal
  Qsag.MigrationExecution.settle_replay_rejected
  Qsag.MigrationExecution.settle_accept_inserts
  Qsag.MigrationExecution.settle_accepted_iff
  Qsag.MigrationExecution.settle_reject_ledger_unchanged
  Qsag.MigrationExecution.settle_spent_monotone
  Qsag.MigrationExecution.settleMany_spent_monotone
  Qsag.MigrationExecution.accepted_nullifier_rejected_after_any_history
  Qsag.MigrationExecution.settlement_acceptance_witness
  Qsag.MigrationExecution.tooth_replay_guard_removal

end MigrationExecution

/-! ## 9. Module-Wide `#verify_constructive` Gate -/

#verify_constructive
  Qsag.odd_not_dvd_two_pow
  Qsag.scalarMulKey_xor_oneBit
  Qsag.canonicalSubgroupHom_scalarMulKey_val
  Qsag.canonicalSubgroupHom_injective_on_canonical
  Qsag.tooth_shor_crqc_breaks_legacy_pk_pre_migration
  Qsag.post_ceremony_nullifier_domain_binding_and_replay_sound
  Qsag.shareUniformLanesCheck_implies_uniform_witness_across_lanes
  Qsag.tooth_non_uniform_lanes_split_witness_across_reps
  Qsag.tooth_premature_residual_open_recovers_spending_key
  Qsag.tooth_premature_residual_open_recovers_canonical_spending_key
  Qsag.verifyAllPendingGf2128_honest_complete
  Qsag.exists_eval_nonzero_tower128
  Qsag.bbcggi19_gf2128_soundness_bound
  Qsag.tooth_unverified_mul_forges_all_outputs_zero
  Qsag.otSacrificeCheckGf2128_characterize
  Qsag.tooth_fixed_bucket_selective_abort_leaks_wire_bit
  Qsag.coin_permuted_bucketing_hides_wire_and_bounds_double_fault
  Qsag.circuitAllOutputsZero_iff_zero_fault
  Qsag.hardened_co_zk_mpc_zero_test_hides_secret_on_input_fault
  Qsag.hardened_co_zk_mpc_two_keys_zero_advantage_on_fault
  Qsag.upfront_invalid_tape_independent_of_spending_key
  Qsag.tooth_premature_witness_range_in_invalid_tape_leaks_secret_bit
  Qsag.multi_turn_hardened_ceremony_trace_safe
  Qsag.inhabited_migration_256_zero_test_and_tooth
  Qsag.inhabited_coin_permuted_bucketing_witness

/-- Rust runs seven independent 64-lane engines, using 438 of their 448 lanes. -/
def migrationMitRepetitions : Nat := 438
abbrev MigrationWitnessBatches := Fin 7 → RssWitnessLanes3

def migrationRepetitionWitness (batches : MigrationWitnessBatches) (rep : Fin 438) :
    MigrationKey256 :=
  extractRepetitionWitness (batches ⟨rep.val / 64, by omega⟩) (rep.val % 64)

/-- Forks preserve the shared input witness; lane uniformity alone does not imply this. -/
def MigrationBatchConsistent (batches : MigrationWitnessBatches) : Prop :=
  (∀ b, shareUniformLanesCheck (batches b) = true) ∧
  (∀ b, extractRepetitionWitness (batches b) 0 = extractRepetitionWitness (batches 0) 0)

theorem migration_all_438_repetitions_same_witness (batches : MigrationWitnessBatches)
    (h : MigrationBatchConsistent batches) (rep : Fin 438) :
    migrationRepetitionWitness batches rep = extractRepetitionWitness (batches 0) 0 := by
  unfold migrationRepetitionWitness
  exact (shareUniformLanesCheck_implies_uniform_witness_across_lanes.1 _
    (h.1 _) _ 0 (Nat.mod_lt _ (by decide)) (by decide)).trans (h.2 _)

theorem migration_batch_geometry :
    (migrationMitRepetitions + 63) / 64 = 7 ∧
    migrationMitRepetitions = 6 * 64 + 54 ∧ 7 * 64 - migrationMitRepetitions = 10 := by decide

theorem witness_migration_batch_consistent :
    ∃ batches : MigrationWitnessBatches, MigrationBatchConsistent batches := by
  let ks : RssKeyShares3 := ⟨1#256, 2#256, 4#256⟩
  refine ⟨fun _ => buildWitnessLanes3 ks (fun j => expandUniformLane64 ((0#256).getLsbD j.val)), ?_⟩
  exact ⟨fun _ => (shareUniformLanesCheck_implies_uniform_witness_across_lanes.2 ks 0).1,
    fun _ => rfl⟩

#verify_inhabited Qsag.migration_all_438_repetitions_same_witness
  Qsag.witness_migration_batch_consistent

/-! ## 10. Seven engine forks × 64 lanes × two instances: the ceremony-level sacrifice bound

`co_zk_mpc.rs:150-155, 232-239` evaluates `MIT_REPETITIONS.div_ceil(64) = 7` batches.
Repetition `rep` is lane `rep % 64` of batch `rep / 64` (`co_zk_mpc.rs:237-246`,
`279-282`). Each batch runs `compute_batch`, which ends in its own
`verify_all_pending` (`co_zk_mpc.rs:320-325`), so every batch has its own flush with
its own coin flips: a forked batch has a separate engine on the session
`QSAG.OUTER.BATCH.V1 ‖ session ‖ batch` (`co_zk_mpc.rs:411-424`), and the unforked
path flips fresh coins per flush on one engine (`outer_mpc.rs:1253-1259`). Any
failing batch aborts the ceremony (`co_zk_mpc.rs:446-456`), before the
`QSAG.OUTER.PRECOMMIT.V1` barrier and every opening (`co_zk_mpc.rs:193-198`).
All 64 lanes of every batch are checked, the ten spare lanes of batch 6 included.

The model in §10 (`flush_false_lane_accepting_coins_bound`) starts at the first
inner-product claims and parameterizes over `FalseRepetitionGivesFalseClaims` (`hLink`).
Section 11 right below discharges `hLink` constructively (`circuit_round0_discharges_hLink`
and `migration_unconditional_circuit_to_sacrifice_ceremony_bound`) by proving both
the circuit-to-`PendingAnd` fault link (`false_witness_implies_pending_and_fault`)
and the `γ`-combiner + degree-30 round-0 polynomial reduction (`round0IpClaim_err_eq_evalCoeffs`;
numerator `54` for the `D0_BITS = 16` packing, which the current `outer_mpc.rs` replaced by
the numerator-`63` packing counted by `rust_bit_check_numerator_63_bound`). The prime-field checks of the
same flush (`outer_mpc.rs:2196, 2474`) are not modelled. -/

namespace MigrationExecution

/-- The engine fork of a repetition, `rep / 64` (`co_zk_mpc.rs:237-246`). -/
def repetitionFork (rep : Fin 438) : Fin 7 := ⟨rep.val / 64, by omega⟩

/-- The bitsliced lane of a repetition inside its fork, `rep % 64`. -/
def repetitionLane (rep : Fin 438) : Fin 64 := ⟨rep.val % 64, by omega⟩

/-- Distinct repetitions occupy distinct `(fork, lane)` slots, the last fork uses
    lanes `0..53` only, and the slot is the one `migrationRepetitionWitness` reads. -/
theorem repetition_slot_geometry :
    (∀ a b : Fin 438, repetitionFork a = repetitionFork b →
      repetitionLane a = repetitionLane b → a = b) ∧
    (∀ rep : Fin 438, repetitionFork rep = 6 → (repetitionLane rep).val < 54) ∧
    (∀ (batches : MigrationWitnessBatches) (rep : Fin 438),
      migrationRepetitionWitness batches rep =
        extractRepetitionWitness (batches (repetitionFork rep)) (repetitionLane rep).val) := by
  refine ⟨fun a b hf hl => ?_, fun rep hf => ?_, fun _ _ => rfl⟩
  · have h1 : a.val / 64 = b.val / 64 := congrArg Fin.val hf
    have h2 : a.val % 64 = b.val % 64 := congrArg Fin.val hl
    exact Fin.ext (by omega)
  · have h1 : rep.val / 64 = 6 := congrArg Fin.val hf
    show rep.val % 64 < 54
    omega

/-- One flush coin vector per engine fork. -/
abbrev CeremonyCoins := Fin 7 → List CoinPair

/-- The ceremony prover: one flush strategy tree per fork. A fork's tree may be
    chosen from the coins of all forks; `FalseRepetition.ownCoins` then removes the
    dependence on the fork's own vector, whose coins reach the prover only through
    its tree. Letting the tree see every other fork's whole vector covers every
    interleaving of the concurrent forks. -/
abbrev CeremonyProver (r : Nat) := Fin 7 → CeremonyCoins → FlushProver r

def setForkCoins (coins : CeremonyCoins) (b : Fin 7) (v : List CoinPair) : CeremonyCoins :=
  fun b' => if b' = b then v else coins b'

/-- The ceremony proceeds only if the flush of every one of the seven forks accepts. -/
def ceremonyAccepts (r : Nat) (p : CeremonyProver r) (cl : Fin 7 → FlushClaims)
    (coins : CeremonyCoins) : Bool :=
  finAll 7 (fun b => flushAccepts r (p b coins) (cl b) (coins b))

/-- Repetition `rep` carries false first claims in both instances of its lane, and
    its fork's strategy tree is fixed before that fork's coins. -/
structure FalseRepetition (r : Nat) (p : CeremonyProver r) (cl : Fin 7 → FlushClaims)
    (rep : Fin 438) : Prop where
  ownCoins : ∀ (c : CeremonyCoins) (v : List CoinPair),
    p (repetitionFork rep) (setForkCoins c (repetitionFork rep) v) = p (repetitionFork rep) c
  false0 : (cl (repetitionFork rep) 0 (repetitionLane rep)).err ≠ 0#128
  false1 : (cl (repetitionFork rep) 1 (repetitionLane rep)).err ≠ 0#128

/-- **Ceremony weld, any coin supports.** For any repetition with false claims and any
    coins of the other six forks, the coin vectors of the repetition's own fork on
    which the seven-fork ceremony accepts number at most `sacrificeBadCoinBound²`. -/
theorem ceremony_false_repetition_accepting_coins_bound
    (S Sb : List RustGf128) (hS : S.Nodup) (hSb : Sb.Nodup) (r : Nat)
    (p : CeremonyProver r) (cl : Fin 7 → FlushClaims) (rep : Fin 438)
    (h : FalseRepetition r p cl rep) (others : CeremonyCoins) :
    ((flushCoinVectors S Sb r).filter (fun v =>
      ceremonyAccepts r p cl (setForkCoins others (repetitionFork rep) v))).length ≤
      sacrificeBadCoinBound S.length Sb.length r * sacrificeBadCoinBound S.length Sb.length r := by
  have hImp : ∀ v, ceremonyAccepts r p cl (setForkCoins others (repetitionFork rep) v) = true →
      flushAccepts r (p (repetitionFork rep) others) (cl (repetitionFork rep)) v = true := by
    intro v hv
    have hb : flushAccepts r
        (p (repetitionFork rep) (setForkCoins others (repetitionFork rep) v))
        (cl (repetitionFork rep))
        (setForkCoins others (repetitionFork rep) v (repetitionFork rep)) = true :=
      (finAll_eq_true_iff 7 _).mp hv (repetitionFork rep)
    have hSelf : setForkCoins others (repetitionFork rep) v (repetitionFork rep) = v :=
      cIte_pos rfl _ _
    rw [h.ownCoins, hSelf] at hb
    exact hb
  have hLe := filter_length_le_of_imp
    (fun v => ceremonyAccepts r p cl (setForkCoins others (repetitionFork rep) v))
    (flushAccepts r (p (repetitionFork rep) others) (cl (repetitionFork rep))) hImp
    (flushCoinVectors S Sb r)
  have hB := flush_false_lane_accepting_coins_bound S Sb hS hSb r
    (p (repetitionFork rep) others) (cl (repetitionFork rep)) (repetitionLane rep)
    h.false0 h.false1
  rw [flushAccepting_eq_filter] at hB
  exact Nat.le_trans hLe hB

/-- Fold coins: all of `GF(2^128)` (`squeeze_u128`, `outer_mpc.rs:236-240, 1818-1823`). -/
def productionFoldCoins : List RustGf128 := (List.finRange (2 ^ 128)).map BitVec.ofFin

/-- Base coins: the nonzero elements (`squeeze_nonzero_u128`, `outer_mpc.rs:242-249,
    2039-2044`). -/
def productionBaseCoins : List RustGf128 :=
  (List.finRange (2 ^ 128 - 1)).map (fun i => BitVec.ofNat 128 (i.val + 1))

theorem productionFoldCoins_card : productionFoldCoins.length = 2 ^ 128 := by
  simp only [productionFoldCoins, List.length_map, List.length_finRange]

theorem productionBaseCoins_card : productionBaseCoins.length = 2 ^ 128 - 1 := by
  simp only [productionBaseCoins, List.length_map, List.length_finRange]

theorem productionFoldCoins_nodup : productionFoldCoins.Nodup := by
  apply List.pairwise_map.mpr
  exact (List.nodup_finRange (2 ^ 128)).imp (fun hne heq => hne (BitVec.ofFin.inj heq))

theorem productionBaseCoins_nodup : productionBaseCoins.Nodup := by
  apply List.pairwise_map.mpr
  refine (List.nodup_finRange (2 ^ 128 - 1)).imp (fun {a b} hne heq => hne ?_)
  have hv := congrArg BitVec.toNat heq
  have ha : a.val + 1 < 2 ^ 128 := by omega
  have hb : b.val + 1 < 2 ^ 128 := by omega
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hv
  exact Fin.ext (by omega)

/-- At the production supports and up to the thirteen binary folds of a full flush
    (`MAX_PENDING_BITS / D0_BITS = 8192` blocks, `outer_mpc.rs:16-33`), the squared
    bad-coin bound is below `2^-246` of the coin space, and the single-instance bound
    is at most `28 / (2^128 - 1)`: the `2 · 13 + 2` fold and base terms. A full flush of the
    current `outer_mpc.rs` has `18` halving rounds; `rust_bit_check_numerator_63_bound` covers
    that count. -/
theorem production_sacrifice_bound : ∀ r, r ≤ 13 →
    sacrificeBadCoinBound (2 ^ 128) (2 ^ 128 - 1) r *
        sacrificeBadCoinBound (2 ^ 128) (2 ^ 128 - 1) r * 2 ^ 246 ≤
      ((2 ^ 128) ^ r * (2 ^ 128 - 1)) * ((2 ^ 128) ^ r * (2 ^ 128 - 1)) ∧
    sacrificeBadCoinBound (2 ^ 128) (2 ^ 128 - 1) r * (2 ^ 128 - 1) ≤
      28 * ((2 ^ 128) ^ r * (2 ^ 128 - 1)) := by
  decide +kernel

/-- **Ceremony weld at the production geometry.** Seven forks, 64 lanes each, 438
    repetitions, two lockstep instances, fold coins over `GF(2^128)`, nonzero base
    coins, at most thirteen folds: a repetition with false claims survives on fewer
    than `2^-246` of its fork's coin vectors, whatever the other forks' coins are. -/
theorem migration_ceremony_false_repetition_below_2_pow_neg_246
    (r : Nat) (hr : r ≤ 13) (p : CeremonyProver r) (cl : Fin 7 → FlushClaims) (rep : Fin 438)
    (h : FalseRepetition r p cl rep) (others : CeremonyCoins) :
    ((flushCoinVectors productionFoldCoins productionBaseCoins r).filter (fun v =>
      ceremonyAccepts r p cl (setForkCoins others (repetitionFork rep) v))).length * 2 ^ 246 ≤
      (flushCoinVectors productionFoldCoins productionBaseCoins r).length := by
  have hB := ceremony_false_repetition_accepting_coins_bound productionFoldCoins
    productionBaseCoins productionFoldCoins_nodup productionBaseCoins_nodup r p cl rep h others
  rw [productionFoldCoins_card, productionBaseCoins_card] at hB
  rw [flushCoinVectors_length, productionFoldCoins_card, productionBaseCoins_card]
  exact Nat.le_trans (Nat.mul_le_mul_right _ hB) (production_sacrifice_bound r hr).1

/-- Every fork's strategy tree is fixed before that fork's own coins. -/
def ForkStrategiesPrecedeOwnCoins {r : Nat} (p : CeremonyProver r) : Prop :=
  ∀ (b : Fin 7) (c : CeremonyCoins) (v : List CoinPair), p b (setForkCoins c b v) = p b c

/-- Link predicate from the circuit to the sacrifice: a repetition whose witness
    fails `rel` has false first inner-product claims in both instances of its lane.
    Discharged constructively in §11 (`circuit_round0_discharges_hLink` and
    `migration_unconditional_circuit_to_sacrifice_ceremony_bound`) outside the
    explicit `γ`-combiner (`≤ 1 / 2^128`) and degree-30 round-0 (`≤ 30 / 2^128`
    per instance, `outer_mpc.rs:1557-1776`) bad coin sets. -/
def FalseRepetitionGivesFalseClaims (batches : MigrationWitnessBatches)
    (rel : MigrationKey256 → Prop) (cl : Fin 7 → FlushClaims) : Prop :=
  ∀ rep : Fin 438, ¬ rel (migrationRepetitionWitness batches rep) →
    (cl (repetitionFork rep) 0 (repetitionLane rep)).err ≠ 0#128 ∧
    (cl (repetitionFork rep) 1 (repetitionLane rep)).err ≠ 0#128

/-- **Same witness, every repetition, every fork.** All 438 repetitions evaluate the
    one shared witness (`migration_all_438_repetitions_same_witness`), so a statement
    that is false for it is false in every repetition. Given `hLink` (discharged in
    `circuit_round0_discharges_hLink` below), every repetition faces the production
    bound in its own fork. -/
theorem migration_false_statement_faces_sacrifice_in_every_repetition
    (batches : MigrationWitnessBatches) (hB : MigrationBatchConsistent batches)
    (rel : MigrationKey256 → Prop) (hFalse : ¬ rel (extractRepetitionWitness (batches 0) 0))
    (r : Nat) (hr : r ≤ 13) (p : CeremonyProver r) (cl : Fin 7 → FlushClaims)
    (hOwn : ForkStrategiesPrecedeOwnCoins p)
    (hLink : FalseRepetitionGivesFalseClaims batches rel cl) :
    ∀ (rep : Fin 438) (others : CeremonyCoins),
      ¬ rel (migrationRepetitionWitness batches rep) ∧
      ((flushCoinVectors productionFoldCoins productionBaseCoins r).filter (fun v =>
        ceremonyAccepts r p cl (setForkCoins others (repetitionFork rep) v))).length * 2 ^ 246 ≤
        (flushCoinVectors productionFoldCoins productionBaseCoins r).length := by
  intro rep others
  have hRep : ¬ rel (migrationRepetitionWitness batches rep) := by
    rw [migration_all_438_repetitions_same_witness batches hB rep]
    exact hFalse
  obtain ⟨h0, h1⟩ := hLink rep hRep
  exact ⟨hRep, migration_ceremony_false_repetition_below_2_pow_neg_246 r hr p cl rep
    ⟨hOwn _, h0, h1⟩ others⟩

/-- The strategy that sends one fixed message everywhere. -/
def constFlushProver (fm : FoldMessage) (bm : BaseMessage) : (r : Nat) → FlushProver r
  | 0 => fun _ _ => bm
  | r + 1 => (fun _ _ => fm, fun _ => constFlushProver fm bm r)

private theorem rustDot_zero_right (a : Nat → RustGf128) : ∀ n,
    rustDot n a (fun _ => 0#128) = 0#128
  | 0 => rfl
  | n + 1 => by
    show rustDot n a (fun _ => 0#128) ^^^ rustGf128Mul (a n) 0#128 = 0#128
    rw [rustDot_zero_right a n, rustGf128Mul_zero_right, BitVec.xor_zero]

/-- A false repetition at the production geometry: thirteen folds over `8192`
    blocks, the last repetition `437` (fork 6, lane 53). -/
theorem inhabited_false_repetition :
    ∃ (p : CeremonyProver 13) (cl : Fin 7 → FlushClaims) (rep : Fin 438),
      FalseRepetition 13 p cl rep := by
  have hErr : (⟨8192, fun _ => 1#128, fun _ => 0#128, 1#128⟩ : IpClaim).err ≠ 0#128 := by
    show rustDot 8192 (fun _ => 1#128) (fun _ => 0#128) ^^^ 1#128 ≠ 0#128
    rw [rustDot_zero_right]
    decide
  exact ⟨fun _ _ => constFlushProver ⟨0#128, 0#128⟩ ⟨0#128, 0#128, 0#128, 0#128⟩ 13,
    fun _ _ _ => ⟨8192, fun _ => 1#128, fun _ => 0#128, 1#128⟩, ⟨437, by decide⟩,
    ⟨fun _ _ => rfl, hErr, hErr⟩⟩

#verify_inhabited Qsag.MigrationExecution.migration_ceremony_false_repetition_below_2_pow_neg_246
  Qsag.MigrationExecution.inhabited_false_repetition

/-- The relation "the key is the scalar one" used by the witness below. -/
def KeyIsScalarOne (k : MigrationKey256) : Prop := k = 1#256

/-- The hypotheses of `migration_false_statement_faces_sacrifice_in_every_repetition`
    hold together: seven consistent forks sharing the key `7`, the relation
    `KeyIsScalarOne` it fails, coin-oblivious fork strategies, and claims that are
    false in every lane. -/
theorem inhabited_false_statement_ceremony :
    ∃ (batches : MigrationWitnessBatches) (p : CeremonyProver 13) (cl : Fin 7 → FlushClaims),
      MigrationBatchConsistent batches ∧
      ¬ KeyIsScalarOne (extractRepetitionWitness (batches 0) 0) ∧
      ForkStrategiesPrecedeOwnCoins p ∧
      FalseRepetitionGivesFalseClaims batches KeyIsScalarOne cl := by
  have hErr : (⟨8192, fun _ => 1#128, fun _ => 0#128, 1#128⟩ : IpClaim).err ≠ 0#128 := by
    show rustDot 8192 (fun _ => 1#128) (fun _ => 0#128) ^^^ 1#128 ≠ 0#128
    rw [rustDot_zero_right]
    decide
  have hW := shareUniformLanesCheck_implies_uniform_witness_across_lanes.2
    ⟨1#256, 2#256, 4#256⟩ 0#256
  have hKey : ¬ KeyIsScalarOne (extractRepetitionWitness
      (buildWitnessLanes3 ⟨1#256, 2#256, 4#256⟩
        (fun j => expandUniformLane64 ((0#256).getLsbD j.val))) 0) := by
    intro h
    have h7 := (hW.2 0 (by decide)).symm.trans h
    revert h7
    decide
  exact ⟨fun _ => buildWitnessLanes3 ⟨1#256, 2#256, 4#256⟩
      (fun j => expandUniformLane64 ((0#256).getLsbD j.val)),
    fun _ _ => constFlushProver ⟨0#128, 0#128⟩ ⟨0#128, 0#128, 0#128, 0#128⟩ 13,
    fun _ _ _ => ⟨8192, fun _ => 1#128, fun _ => 0#128, 1#128⟩,
    ⟨fun _ => hW.1, fun _ => rfl⟩, hKey, fun _ _ _ => rfl, fun _ _ => ⟨hErr, hErr⟩⟩

#verify_inhabited
  Qsag.MigrationExecution.migration_false_statement_faces_sacrifice_in_every_repetition
  Qsag.MigrationExecution.inhabited_false_statement_ceremony

#verify_constructive
  Qsag.MigrationExecution.flushBaseAccepts_checks_all_openings
  Qsag.MigrationExecution.flushAccepting_eq_filter
  Qsag.MigrationExecution.flushCoinVectors_length
  Qsag.MigrationExecution.flush_false_lane_accepting_coins_bound
  Qsag.MigrationExecution.flush_one_false_instance_accepting_coins_bound
  Qsag.MigrationExecution.repetition_slot_geometry
  Qsag.MigrationExecution.ceremony_false_repetition_accepting_coins_bound
  Qsag.MigrationExecution.productionFoldCoins_nodup
  Qsag.MigrationExecution.productionBaseCoins_nodup
  Qsag.MigrationExecution.production_sacrifice_bound
  Qsag.MigrationExecution.migration_ceremony_false_repetition_below_2_pow_neg_246
  Qsag.MigrationExecution.migration_false_statement_faces_sacrifice_in_every_repetition
  Qsag.MigrationExecution.inhabited_false_repetition

/-! ## 11. Constructive Circuit-to-Sacrifice Link (`γ`-Combiner + Degree-30 Round 0) & 438-Repetition QROM Soundness

This section discharges `FalseRepetitionGivesFalseClaims` (`hLink`) constructively and proves the
unconditional end-to-end 438-repetition ceremony + QROM Fiat–Shamir soundness bound matching
`verify_pending_bits_slice` (`crates/qsag-migrate/src/outer_mpc.rs:16-45, 1557-1776`):
1. **Circuit-to-`PendingAnd` Fault Link (`false_witness_implies_pending_and_fault`)**:
   If a Boolean gate trace `gates` is sound for `relB : MigrationKey256 → Bool` and evaluates a
   false witness (`relB (extractRepetitionWitness witness lane.val) = false`) to an opened `true`
   output bit in `lane`, then at least one `PendingAnd` triple in `st.pending` has `laneErr = true`.
2. **128-Gate Super-Block Packing + `γ`-Combiner (`superBlockDefect_ne_zero_of_gateErr`,
   `gammaCombinedDefect_bad_coins_le_one`)**:
   Packing 128 gate bits onto `{1, X, …, X^127}` in `RustGf128` is lossless (`0` collision error
   inside a 128-gate super-block), and combining `numSuper` super-blocks with uniform `gammas`
   survives on at most `1` bad `γ` coin (`≤ 2^-128`).
3. **Degree-30 Round-0 Polynomial Reduction (`round0IpClaim_err_eq_evalCoeffs`,
   `round0_false_gamma_survives_at_most_30_coins`)**:
   Packing `8` blocks of `D0_BITS = 16` gates per super-block (`DEG_R0 = 31`, `HALF_R0 = 15`), the
   Round-0 inner-product defect `(round0IpClaim … r0 lane).err` is a formal degree-`≤ 30` polynomial
   in `r0` whose `r0^15` coefficient equals `gammaCombinedDefect` (independent of the prover's 30
   reshared cross-terms `h0`), surviving on at most `30` coins per instance (numerator
   `30 + 2 * 11 + 2 = 54` at `r = 11` for this `D0_BITS = 16` packing; the current Rust
   `BIT_CHECK_NUMERATOR` is `63`, see `rust_bit_check_numerator_63_bound`).
4. **Unconditional `hLink` Discharge & 438-Repetition Ceremony + QROM Composition
   (`circuit_round0_discharges_hLink`, `migration_unconditional_circuit_to_sacrifice_ceremony_bound`,
   `migration_438_zkboo_and_ceremony_qrom_soundness`)**:
   Eliminates the unproved `hLink` hypothesis across all 438 repetitions (`7` forks × `64` lanes)
   and composes the active-MPC flush bound with the 438-repetition ZKBoo QROM Grover bound. -/

/-- General root-witness transfer from `Tower128` (`exists_eval_nonzero_tower128`) to `RustGf128`
    via the field isomorphism `rustToTower` / `towerToRust`. -/
private theorem evalCoeffs_map_rustToTower :
    ∀ (cs : List RustGf128) (x : RustGf128),
      RoundPoly.evalCoeffs (cs.map rustToTower) (rustToTower x) =
        rustToTower (RoundPoly.evalCoeffs cs x)
  | [], _ => rustToTower_zero.symm
  | c :: tail, x => by
    simp only [List.map_cons, RoundPoly.evalCoeffs_cons]
    change towerAdd 7 (rustToTower c)
        (towerMul 7 (rustToTower x) (RoundPoly.evalCoeffs (tail.map rustToTower) (rustToTower x))) =
      rustToTower (c ^^^ rustGf128Mul x (RoundPoly.evalCoeffs tail x))
    rw [evalCoeffs_map_rustToTower tail x, ← rustToTower_mul, ← rustToTower_xor]

theorem exists_eval_nonzero_rustGf128 (cs : List RustGf128)
    (hLen : cs.length < 2 ^ 128) (hEx : ∃ c ∈ cs, c ≠ 0#128) :
    ∃ x₀ : RustGf128, RoundPoly.evalCoeffs cs x₀ ≠ CommRingOps.zero := by
  obtain ⟨c, hcMem, hcNe⟩ := hEx
  have hcTowerNe : rustToTower c ≠ towerZero 7 := by
    intro hZero
    exact hcNe (rustToTower_injective c 0#128 (hZero.trans rustToTower_zero.symm))
  have hLenMap : (cs.map rustToTower).length < 2 ^ 128 := by
    rw [List.length_map]; exact hLen
  obtain ⟨t₀, ht₀⟩ := exists_eval_nonzero_tower128 (cs.map rustToTower) hLenMap
    ⟨rustToTower c, List.mem_map_of_mem hcMem, hcTowerNe⟩
  refine ⟨towerToRust 7 t₀, ?_⟩
  intro hZero
  have hEval := evalCoeffs_map_rustToTower cs (towerToRust 7 t₀)
  rw [rustToTower_towerToRust] at hEval
  have hZeroRust : RoundPoly.evalCoeffs cs (towerToRust 7 t₀) = 0#128 := hZero
  rw [hZeroRust, rustToTower_zero] at hEval
  exact ht₀ hEval

/-- Structural zero-padded coefficient lookup on `List RustGf128` (`0` WHNF overhead). -/
def coeffAt : List RustGf128 → Nat → RustGf128
  | [], _ => 0#128
  | c :: _, 0 => c
  | _ :: cs, k + 1 => coeffAt cs k

theorem exists_mem_ne_zero_of_coeffAt :
    ∀ (cs : List RustGf128) (k : Nat),
      coeffAt cs k ≠ 0#128 → ∃ c ∈ cs, c ≠ 0#128
  | [], _, h => absurd rfl h
  | c :: _, 0, h => ⟨c, .head _, h⟩
  | _ :: tail, k + 1, h => by
    obtain ⟨c', hm, hne⟩ := exists_mem_ne_zero_of_coeffAt tail k h
    exact ⟨c', .tail _ hm, hne⟩

theorem rustGf128_roots_le_of_coeffAt_nonzero (d : Nat) (cs : List RustGf128) (k : Nat)
    (S : List RustGf128) (hS : S.Nodup) (hLen : cs.length ≤ d + 1) (hdLt : d + 1 < 2 ^ 128)
    (hkNe : coeffAt cs k ≠ 0#128) :
    (S.filter (fun r => decide (RoundPoly.evalCoeffs cs r = CommRingOps.zero))).length ≤ d :=
  RoundPoly.roots_nodup_length_le d cs S hS hLen
    (exists_eval_nonzero_rustGf128 cs (Nat.lt_of_le_of_lt hLen hdLt)
      (exists_mem_ne_zero_of_coeffAt cs k hkNe))

/-- Reconstructed bit of a 3-share 64-lane wire word in `lane`. -/
def wireBit (w : RssWord64Shares3) (lane : Fin 64) : Bool :=
  w.reconstruct.toBitVec.getLsbD lane.val

theorem uint64_xor_getLsbD (a b : UInt64) (k : Nat) :
    (a ^^^ b).toBitVec.getLsbD k = ((a.toBitVec.getLsbD k) ^^ (b.toBitVec.getLsbD k)) := by
  cases a with
  | ofBitVec _ =>
    cases b with
    | ofBitVec _ =>
      exact BitVec.getLsbD_xor

theorem uint64_and_getLsbD (a b : UInt64) (k : Nat) :
    (a &&& b).toBitVec.getLsbD k = (a.toBitVec.getLsbD k && b.toBitVec.getLsbD k) := by
  cases a with
  | ofBitVec _ =>
    cases b with
    | ofBitVec _ =>
      exact BitVec.getLsbD_and

theorem xorShares_wireBit (a b : RssWord64Shares3) (lane : Fin 64) :
    wireBit (xorShares a b) lane = ((wireBit a lane) ^^ (wireBit b lane)) := by
  unfold wireBit xorShares RssWord64Shares3.reconstruct
  simp only [uint64_xor_getLsbD]
  cases a.w0.toBitVec.getLsbD lane.val <;>
    cases a.w1.toBitVec.getLsbD lane.val <;>
    cases a.w2.toBitVec.getLsbD lane.val <;>
    cases b.w0.toBitVec.getLsbD lane.val <;>
    cases b.w1.toBitVec.getLsbD lane.val <;>
    cases b.w2.toBitVec.getLsbD lane.val <;> rfl

/-- Per-lane Boolean multiplication error bit `z_lane ⊕ (x_lane ∧ y_lane)`. -/
def PendingAnd.laneErr (t : PendingAnd) (lane : Fin 64) : Bool :=
  (wireBit t.output lane) ^^ (wireBit t.lhs lane && wireBit t.rhs lane)

theorem laneErr_eq_false_iff (t : PendingAnd) (lane : Fin 64) :
    t.laneErr lane = false ↔ wireBit t.output lane = (wireBit t.lhs lane && wireBit t.rhs lane) := by
  unfold PendingAnd.laneErr
  cases wireBit t.output lane <;> cases (wireBit t.lhs lane && wireBit t.rhs lane) <;> decide

/-- Pure single-lane Boolean gate semantics matching `evalGate` wire-for-wire. -/
def evalGateBool (ws : List Bool) : Gate → Option (List Bool)
  | .xor l r =>
    match ws[l]?, ws[r]? with
    | some a, some b => some ((a ^^ b) :: ws)
    | _, _ => none
  | .and l r _ =>
    match ws[l]?, ws[r]? with
    | some a, some b => some ((a && b) :: ws)
    | _, _ => none

/-- Pure single-lane Boolean circuit semantics matching `evalGates`. -/
def evalGatesBool : List Bool → List Gate → Option (List Bool)
  | ws, [] => some ws
  | ws, g :: gs => (evalGateBool ws g).bind (fun next => evalGatesBool next gs)

theorem evalGate_pending_subset {st next : GateState} {g : Gate}
    (h : evalGate st g = some next) : ∀ t ∈ st.pending, t ∈ next.pending := by
  cases g with
  | xor l r =>
    simp only [evalGate] at h
    cases hl : st.wires[l]? with
    | none => rw [hl] at h; cases h
    | some a =>
      cases hr : st.wires[r]? with
      | none => rw [hl, hr] at h; cases h
      | some b =>
        rw [hl, hr] at h
        injection h with hNext
        subst hNext
        intro t ht; exact ht
  | and l r out =>
    simp only [evalGate] at h
    cases hl : st.wires[l]? with
    | none => rw [hl] at h; cases h
    | some a =>
      cases hr : st.wires[r]? with
      | none => rw [hl, hr] at h; cases h
      | some b =>
        rw [hl, hr] at h
        injection h with hNext
        subst hNext
        intro t ht; exact .tail _ ht

theorem evalGates_pending_subset :
    ∀ (gs : List Gate) {st final : GateState},
      evalGates st gs = some final → ∀ t ∈ st.pending, t ∈ final.pending
  | [], _, _, h, t, ht => by injection h with hEq; subst hEq; exact ht
  | g :: gs, st, final, h, t, ht => by
    simp only [evalGates] at h
    cases hg : evalGate st g with
    | none => rw [hg] at h; cases h
    | some mid =>
      rw [hg] at h
      exact evalGates_pending_subset gs h t (evalGate_pending_subset hg t ht)

theorem evalGate_lane_sound {st next : GateState} {g : Gate} (lane : Fin 64)
    (h : evalGate st g = some next)
    (hPend : ∀ t ∈ next.pending, t.laneErr lane = false) :
    evalGateBool (st.wires.map (fun w => wireBit w lane)) g =
      some (next.wires.map (fun w => wireBit w lane)) := by
  cases g with
  | xor l r =>
    simp only [evalGate] at h
    cases hl : st.wires[l]? with
    | none => rw [hl] at h; cases h
    | some a =>
      cases hr : st.wires[r]? with
      | none => rw [hl, hr] at h; cases h
      | some b =>
        rw [hl, hr] at h
        injection h with hNext
        subst hNext
        simp only [evalGateBool, List.getElem?_map, hl, hr, Option.map_some, List.map_cons,
          xorShares_wireBit]
  | and l r out =>
    simp only [evalGate] at h
    cases hl : st.wires[l]? with
    | none => rw [hl] at h; cases h
    | some a =>
      cases hr : st.wires[r]? with
      | none => rw [hl, hr] at h; cases h
      | some b =>
        rw [hl, hr] at h
        injection h with hNext
        subst hNext
        have hOutEq : wireBit out lane = (wireBit a lane && wireBit b lane) :=
          (laneErr_eq_false_iff ⟨a, b, out⟩ lane).mp (hPend ⟨a, b, out⟩ (.head _))
        simp only [evalGateBool, List.getElem?_map, hl, hr, Option.map_some, List.map_cons, hOutEq]

theorem evalGates_lane_sound :
    ∀ (gs : List Gate) {st final : GateState} (lane : Fin 64),
      evalGates st gs = some final →
      (∀ t ∈ final.pending, t.laneErr lane = false) →
      evalGatesBool (st.wires.map (fun w => wireBit w lane)) gs =
        some (final.wires.map (fun w => wireBit w lane))
  | [], _, _, _, h, _ => by
    injection h with hEq; subst hEq; rfl
  | g :: gs, st, final, lane, h, hPend => by
    simp only [evalGates] at h
    cases hg : evalGate st g with
    | none => rw [hg] at h; cases h
    | some mid =>
      rw [hg] at h
      have hMidPend : ∀ t ∈ mid.pending, t.laneErr lane = false :=
        fun t ht => hPend t (evalGates_pending_subset gs h t ht)
      have hStep := evalGate_lane_sound lane hg hMidPend
      simp only [evalGatesBool, hStep, Option.bind_some]
      exact evalGates_lane_sound gs lane h hPend

theorem witnessWires_map_wireBit (witness : RssWitnessLanes3) (lane : Fin 64) :
    (witnessWires witness).map (fun w => wireBit w lane) =
      List.ofFn (fun i : Fin 256 => (extractRepetitionWitness witness lane.val).getLsbD i.val) := by
  apply List.ext_getElem?
  intro j
  simp only [witnessWires, List.getElem?_map, List.getElem?_ofFn]
  by_cases hj : j < 256
  · simp only [hj, ↓reduceDIte, Option.map_some]
    unfold extractRepetitionWitness wireBit RssWord64Shares3.reconstruct
    rw [packBits_getLsbD 256 _ j hj, cDIte_pos hj]
  · simp only [hj, ↓reduceDIte, Option.map_none]

/-- Pure Boolean circuit soundness contract for `gates` wrt `relB : MigrationKey256 → Bool`. -/
def CircuitSoundForRel (gates : List Gate) (relB : MigrationKey256 → Bool) : Prop :=
  ∀ (w : MigrationKey256) (rest : List Bool),
    evalGatesBool (List.ofFn (fun i : Fin 256 => w.getLsbD i.val)) gates = some (true :: rest) →
    relB w = true

/-- Constructive search for the first faulty `PendingAnd` index in `lane` (`0 Classical.choice`). -/
def findFaultyGateIdx : List PendingAnd → Fin 64 → Option Nat
  | [], _ => none
  | t :: rest, lane =>
    if t.laneErr lane then some 0
    else (findFaultyGateIdx rest lane).map Nat.succ

theorem findFaultyGateIdx_spec :
    ∀ (pending : List PendingAnd) (lane : Fin 64),
      (match findFaultyGateIdx pending lane with
       | some idx => idx < pending.length ∧ (pending[idx]?).map (fun t => t.laneErr lane) = some true
       | none => ∀ t ∈ pending, t.laneErr lane = false)
  | [], _ => fun _ ht => nomatch ht
  | t :: rest, lane => by
    simp only [findFaultyGateIdx]
    cases hErr : t.laneErr lane
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have ih := findFaultyGateIdx_spec rest lane
      cases hFind : findFaultyGateIdx rest lane with
      | none =>
        rw [hFind] at ih
        simp only [Option.map_none]
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hTail
        · exact hErr
        · exact ih x hTail
      | some idx =>
        rw [hFind] at ih
        simp only [Option.map_some, List.length_cons, List.getElem?_cons_succ]
        exact ⟨Nat.succ_lt_succ ih.1, ih.2⟩
    · simp only [↓reduceIte, List.length_cons, Nat.zero_lt_succ, List.getElem?_cons_zero,
        Option.map_some, hErr, and_self]

/-- **Circuit-to-`PendingAnd` Fault Link (`false_witness_implies_pending_and_fault`)**:
    Whenever `gates` is sound for `relB`, `relB (extractRepetitionWitness witness lane.val) = false`,
    and `evalGates ⟨witnessWires witness, []⟩ gates = some st` produces an output wire whose `lane`
    bit reconstructs to `true`, `findFaultyGateIdx` constructively locates an explicit faulty
    `PendingAnd` gate `idx < st.pending.length` in `lane`! -/
theorem false_witness_implies_pending_and_fault
    (gates : List Gate) (relB : MigrationKey256 → Bool)
    (hCirc : CircuitSoundForRel gates relB)
    (witness : RssWitnessLanes3) (lane : Fin 64)
    (hFalse : relB (extractRepetitionWitness witness lane.val) = false)
    (st : GateState) (hEval : evalGates ⟨witnessWires witness, []⟩ gates = some st)
    (hOpenTrue : match st.wires with | out :: _ => wireBit out lane = true | [] => False) :
    ∃ idx : Nat, idx < st.pending.length ∧
      (st.pending[idx]?).map (fun t => t.laneErr lane) = some true := by
  have hSpec := findFaultyGateIdx_spec st.pending lane
  cases hFind : findFaultyGateIdx st.pending lane with
  | some idx =>
    rw [hFind] at hSpec
    exact ⟨idx, hSpec⟩
  | none =>
    rw [hFind] at hSpec
    exfalso
    have hPure := evalGates_lane_sound gates lane hEval hSpec
    dsimp only at hPure
    rw [witnessWires_map_wireBit witness lane] at hPure
    cases hw : st.wires with
    | nil => rw [hw] at hOpenTrue; exact hOpenTrue
    | cons out rest =>
      rw [hw] at hOpenTrue hPure
      dsimp only at hOpenTrue
      simp only [List.map_cons, hOpenTrue] at hPure
      have hRelTrue := hCirc (extractRepetitionWitness witness lane.val)
        (rest.map (fun w => wireBit w lane)) hPure
      rw [hFalse] at hRelTrue
      cases hRelTrue

/-- Finite XOR sum over `RustGf128`. -/
def rustSum : Nat → (Nat → RustGf128) → RustGf128
  | 0, _ => 0#128
  | n + 1, f => rustSum n f ^^^ f n

theorem rustSum_congr (n : Nat) {f g : Nat → RustGf128}
    (h : ∀ i, i < n → f i = g i) : rustSum n f = rustSum n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show rustSum n f ^^^ f n = rustSum n g ^^^ g n
    rw [ih (fun i hi => h i (by omega)), h n (by omega)]

theorem rustSum_xor (n : Nat) (f g : Nat → RustGf128) :
    rustSum n (fun i => f i ^^^ g i) = rustSum n f ^^^ rustSum n g := by
  induction n with
  | zero => simp only [rustSum]; decide
  | succ n ih =>
    show rustSum n (fun i => f i ^^^ g i) ^^^ (f n ^^^ g n) =
      (rustSum n f ^^^ f n) ^^^ (rustSum n g ^^^ g n)
    rw [ih]
    rw [BitVec.xor_assoc (rustSum n f) (rustSum n g) (f n ^^^ g n),
        ← BitVec.xor_assoc (rustSum n g) (f n) (g n),
        BitVec.xor_comm (rustSum n g) (f n),
        BitVec.xor_assoc (f n) (rustSum n g) (g n),
        ← BitVec.xor_assoc (rustSum n f) (f n) (rustSum n g ^^^ g n)]

theorem rustSum_mul_left (c : RustGf128) : ∀ (n : Nat) (f : Nat → RustGf128),
    rustGf128Mul c (rustSum n f) = rustSum n (fun i => rustGf128Mul c (f i))
  | 0, _ => rustGf128Mul_zero_right c
  | n + 1, f => by
    show rustGf128Mul c (rustSum n f ^^^ f n) =
      rustSum n (fun i => rustGf128Mul c (f i)) ^^^ rustGf128Mul c (f n)
    rw [rustGf128Mul_xor_right, rustSum_mul_left c n f]

theorem rustSum_add_split (n : Nat) (f : Nat → RustGf128) : ∀ m : Nat,
    rustSum (n + m) f = rustSum n f ^^^ rustSum m (fun j => f (n + j))
  | 0 => by show rustSum n f = rustSum n f ^^^ 0#128; rw [BitVec.xor_zero]
  | m + 1 => by
    show rustSum (n + m) f ^^^ f (n + m) =
      rustSum n f ^^^ (rustSum m (fun j => f (n + j)) ^^^ f (n + m))
    rw [rustSum_add_split n f m, BitVec.xor_assoc]

theorem rustSum_blocks (B K : Nat) (f : Nat → RustGf128) :
    rustSum (B * K) f = rustSum B (fun b => rustSum K (fun u => f (K * b + u))) := by
  induction B with
  | zero => simp only [Nat.zero_mul, rustSum]
  | succ B ih =>
    have hEq : (B + 1) * K = B * K + K := by rw [Nat.add_mul, Nat.one_mul]
    rw [hEq, rustSum_add_split (B * K) f K, ih]
    show _ = rustSum B _ ^^^ rustSum K (fun u => f (K * B + u))
    congr 1
    apply rustSum_congr
    intro u _
    rw [Nat.mul_comm B K]

/-- Gate bit extractors on `pending : List PendingAnd` (zero-padded past `pending.length`). -/
def gateLhsBit (pending : List PendingAnd) (idx : Nat) (lane : Fin 64) : Bool :=
  match pending[idx]? with | some t => wireBit t.lhs lane | none => false

def gateRhsBit (pending : List PendingAnd) (idx : Nat) (lane : Fin 64) : Bool :=
  match pending[idx]? with | some t => wireBit t.rhs lane | none => false

def gateOutBit (pending : List PendingAnd) (idx : Nat) (lane : Fin 64) : Bool :=
  match pending[idx]? with | some t => wireBit t.output lane | none => false

def gateErrBit (pending : List PendingAnd) (idx : Nat) (lane : Fin 64) : Bool :=
  (gateOutBit pending idx lane) ^^ (gateLhsBit pending idx lane && gateRhsBit pending idx lane)

/-- Pack 128 gate bits onto `{1, X, …, X^127}` in `RustGf128` (`outer_mpc.rs:1593-1642`). -/
def packBlock128 (f : Nat → Bool) : RustGf128 :=
  rustSum 128 (fun k => if f k then BitVec.twoPow 128 k else 0#128)

theorem packBlock128_aux_bit : ∀ (n : Nat), n ≤ 128 → ∀ (f : Nat → Bool) (i : Nat),
    (rustSum n (fun k => if f k then BitVec.twoPow 128 k else 0#128)).getLsbD i =
      (decide (i < n) && f i)
  | 0, _, f, i => by
    simp only [rustSum, BitVec.getLsbD_zero, Nat.not_lt_zero, decide_false, Bool.false_and]
  | n + 1, hn, f, i => by
    show (rustSum n (fun k => if f k then BitVec.twoPow 128 k else 0#128) ^^^
      (if f n then BitVec.twoPow 128 n else 0#128)).getLsbD i = (decide (i < n + 1) && f i)
    rw [BitVec.getLsbD_xor, packBlock128_aux_bit n (by omega) f i, ite_twoPow_bit (f n) n i (by omega)]
    rcases Nat.lt_trichotomy i n with hLt | rfl | hGt
    · rw [decide_eq_true hLt, decide_eq_true (by omega : i < n + 1),
          decide_eq_false (by omega : ¬ n = i)]
      cases f i <;> cases f n <;> rfl
    · rw [decide_eq_false (Nat.lt_irrefl i), decide_eq_true (Nat.lt_succ_self i),
          decide_eq_true (Eq.refl i)]
      cases f i <;> rfl
    · rw [decide_eq_false (by omega : ¬ i < n), decide_eq_false (by omega : ¬ i < n + 1),
          decide_eq_false (by omega : ¬ n = i)]
      cases f i <;> cases f n <;> rfl

theorem packBlock128_getLsbD (f : Nat → Bool) (i : Nat) (hi : i < 128) :
    (packBlock128 f).getLsbD i = f i := by
  unfold packBlock128
  rw [packBlock128_aux_bit 128 (Nat.le_refl 128) f i, decide_eq_true hi, Bool.true_and]

/-- Packed 128-gate `AND` product, claimed `Z` output, and `AND`⊕`Z` defect of super-block `q`. -/
def superBlockAnd (pending : List PendingAnd) (q : Nat) (lane : Fin 64) : RustGf128 :=
  packBlock128 (fun k => gateLhsBit pending (128 * q + k) lane && gateRhsBit pending (128 * q + k) lane)

def superBlockZ (pending : List PendingAnd) (q : Nat) (lane : Fin 64) : RustGf128 :=
  packBlock128 (fun k => gateOutBit pending (128 * q + k) lane)

def superBlockDefect (pending : List PendingAnd) (q : Nat) (lane : Fin 64) : RustGf128 :=
  superBlockAnd pending q lane ^^^ superBlockZ pending q lane

theorem superBlockDefect_ne_zero_of_gateErr (pending : List PendingAnd)
    (numSuper idx : Nat) (lane : Fin 64)
    (hIdx : idx < 128 * numSuper) (hErr : gateErrBit pending idx lane = true) :
    idx / 128 < numSuper ∧ superBlockDefect pending (idx / 128) lane ≠ 0#128 := by
  refine ⟨by omega, ?_⟩
  intro hZero
  have hBit := congrArg (fun v : RustGf128 => v.getLsbD (idx % 128)) hZero
  have hRem : idx % 128 < 128 := Nat.mod_lt idx (by decide)
  have hDivMod : 128 * (idx / 128) + idx % 128 = idx := Nat.div_add_mod idx 128
  unfold superBlockDefect superBlockAnd superBlockZ at hBit
  rw [BitVec.getLsbD_xor, packBlock128_getLsbD _ _ hRem, packBlock128_getLsbD _ _ hRem,
      hDivMod, BitVec.getLsbD_zero] at hBit
  unfold gateErrBit at hErr
  cases hout : gateOutBit pending idx lane <;>
    cases hand : (gateLhsBit pending idx lane && gateRhsBit pending idx lane) <;>
    simp only [hout, hand] at hErr hBit <;>
    cases hErr <;> cases hBit

/-- `γ`-weighted super-block `Z` accumulator (`scratch.step0_acc[0..1]`, `outer_mpc.rs:1648-1654`)
    and `γ`-weighted super-block defect (`∑_{q < numSuper} γ_q · superBlockDefect_q`). -/
def step0ZAcc (pending : List PendingAnd) (numSuper : Nat)
    (gammas : Nat → RustGf128) (lane : Fin 64) : RustGf128 :=
  rustDot numSuper gammas (fun q => superBlockZ pending q lane)

def gammaCombinedDefect (pending : List PendingAnd) (numSuper : Nat)
    (gammas : Nat → RustGf128) (lane : Fin 64) : RustGf128 :=
  rustDot numSuper gammas (fun q => superBlockDefect pending q lane)

def setGammaAt (gammas : Nat → RustGf128) (qStar : Nat) (g : RustGf128) : Nat → RustGf128 :=
  fun q => if q = qStar then g else gammas q

theorem rustDot_setGammaAt :
    ∀ (n : Nat) (gammas : Nat → RustGf128) (d : Nat → RustGf128) (qStar : Nat) (g : RustGf128),
      qStar < n →
      rustDot n (setGammaAt gammas qStar g) d =
        rustDot n (setGammaAt gammas qStar 0#128) d ^^^ rustGf128Mul g (d qStar)
  | 0, _, _, _, _, h => nomatch h
  | n + 1, gammas, d, qStar, g, hLt => by
    rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp hLt) with rfl | hLt'
    · show rustDot qStar (setGammaAt gammas qStar g) d ^^^
          rustGf128Mul (setGammaAt gammas qStar g qStar) (d qStar) =
        (rustDot qStar (setGammaAt gammas qStar 0#128) d ^^^
          rustGf128Mul (setGammaAt gammas qStar 0#128 qStar) (d qStar)) ^^^
        rustGf128Mul g (d qStar)
      have hRest : rustDot qStar (setGammaAt gammas qStar g) d =
          rustDot qStar (setGammaAt gammas qStar 0#128) d := by
        apply rustDot_congr
        · intro i hi
          simp only [setGammaAt, show ¬ i = qStar from by omega, ↓reduceIte]
        · intro _ _; rfl
      simp only [hRest, setGammaAt, ↓reduceIte, rustGf128Mul_zero_left, BitVec.xor_zero]
    · have ih := rustDot_setGammaAt n gammas d qStar g hLt'
      show rustDot n (setGammaAt gammas qStar g) d ^^^
          rustGf128Mul (setGammaAt gammas qStar g n) (d n) =
        (rustDot n (setGammaAt gammas qStar 0#128) d ^^^
          rustGf128Mul (setGammaAt gammas qStar 0#128 n) (d n)) ^^^
        rustGf128Mul g (d qStar)
      rw [ih]
      simp only [setGammaAt, show ¬ n = qStar from by omega, ↓reduceIte]
      rw [BitVec.xor_assoc (rustDot n (setGammaAt gammas qStar 0#128) d)
            (rustGf128Mul g (d qStar)) (rustGf128Mul (gammas n) (d n)),
          BitVec.xor_comm (rustGf128Mul g (d qStar)) (rustGf128Mul (gammas n) (d n)),
          ← BitVec.xor_assoc]

/-- **`γ`-Combiner Soundness (`gammaCombinedDefect_bad_coins_le_one`)**:
    If super-block `qStar < numSuper` has a non-zero packed gate defect, then for any fixed values
    of the other `γ` coordinates and any duplicate-free `S : List RustGf128`, at most `1` value of
    `γ_{qStar} ∈ S` cancels `gammaCombinedDefect` (`≤ 2^-128`). -/
theorem gammaCombinedDefect_bad_coins_le_one
    (pending : List PendingAnd) (numSuper qStar : Nat) (lane : Fin 64)
    (hq : qStar < numSuper)
    (hDefNe : superBlockDefect pending qStar lane ≠ 0#128)
    (otherGammas : Nat → RustGf128)
    (S : List RustGf128) (hS : S.Nodup) :
    (S.filter (fun g =>
      decide (gammaCombinedDefect pending numSuper (setGammaAt otherGammas qStar g) lane = 0#128))).length ≤ 1 := by
  let c0 := rustDot numSuper (setGammaAt otherGammas qStar 0#128)
    (fun q => superBlockDefect pending q lane)
  let c1 := superBlockDefect pending qStar lane
  have hCount := rustGf128_roots_le_of_coeffAt_nonzero 1 [c0, c1] 1 S hS (Nat.le_refl 2) (by decide) hDefNe
  have hPred : (fun g =>
      decide (gammaCombinedDefect pending numSuper (setGammaAt otherGammas qStar g) lane = 0#128)) =
      (fun g => decide (RoundPoly.evalCoeffs [c0, c1] g = CommRingOps.zero)) := by
    funext g
    have hEq : gammaCombinedDefect pending numSuper (setGammaAt otherGammas qStar g) lane =
        RoundPoly.evalCoeffs [c0, c1] g := by
      unfold gammaCombinedDefect
      rw [rustDot_setGammaAt numSuper otherGammas _ qStar g hq]
      show c0 ^^^ rustGf128Mul g c1 = c0 ^^^ rustGf128Mul g (c1 ^^^ rustGf128Mul g 0#128)
      rw [rustGf128Mul_zero_right, BitVec.xor_zero]
    rw [hEq]; rfl
  rw [hPred]; exact hCount

/-! ### Degree-30 Round-0 Polynomial Algebra (`D0_BITS = 16`, `DEG_R0 = 31`, `HALF_R0 = 15`) -/

def polyAddRust : List RustGf128 → List RustGf128 → List RustGf128
  | [], ds => ds
  | cs, [] => cs
  | c :: cs, d :: ds => (c ^^^ d) :: polyAddRust cs ds

def polyScaleRust (c : RustGf128) (cs : List RustGf128) : List RustGf128 :=
  cs.map (rustGf128Mul c)

def polyMulRust : List RustGf128 → List RustGf128 → List RustGf128
  | [], _ => []
  | c :: cs, ds => polyAddRust (polyScaleRust c ds) (0#128 :: polyMulRust cs ds)

def polySumRust : Nat → (Nat → List RustGf128) → List RustGf128
  | 0, _ => []
  | n + 1, f => polyAddRust (polySumRust n f) (f n)

theorem polyAddRust_length : ∀ (a b : List RustGf128),
    (polyAddRust a b).length = Nat.max a.length b.length
  | [], b => by simp only [polyAddRust, List.length_nil, Nat.zero_max]
  | a :: as, [] => by simp only [polyAddRust, List.length_nil, Nat.max_zero]
  | a :: as, b :: bs => by
    simp only [polyAddRust, List.length_cons, polyAddRust_length as bs, Nat.succ_max_succ]

theorem evalCoeffs_polyAddRust : ∀ (a b : List RustGf128) (x : RustGf128),
    RoundPoly.evalCoeffs (polyAddRust a b) x =
      RoundPoly.evalCoeffs a x ^^^ RoundPoly.evalCoeffs b x
  | [], b, _ => by show RoundPoly.evalCoeffs b _ = 0#128 ^^^ _; rw [BitVec.zero_xor]
  | a :: as, [], x => by
    simp only [polyAddRust]
    show RoundPoly.evalCoeffs (a :: as) x = RoundPoly.evalCoeffs (a :: as) x ^^^ 0#128
    rw [BitVec.xor_zero]
  | a :: as, b :: bs, x => by
    show (a ^^^ b) ^^^ rustGf128Mul x (RoundPoly.evalCoeffs (polyAddRust as bs) x) =
      (a ^^^ rustGf128Mul x (RoundPoly.evalCoeffs as x)) ^^^
      (b ^^^ rustGf128Mul x (RoundPoly.evalCoeffs bs x))
    rw [evalCoeffs_polyAddRust as bs x, rustGf128Mul_xor_right]
    rw [BitVec.xor_assoc a (rustGf128Mul x (RoundPoly.evalCoeffs as x))
          (b ^^^ rustGf128Mul x (RoundPoly.evalCoeffs bs x)),
        ← BitVec.xor_assoc (rustGf128Mul x (RoundPoly.evalCoeffs as x)) b
          (rustGf128Mul x (RoundPoly.evalCoeffs bs x)),
        BitVec.xor_comm (rustGf128Mul x (RoundPoly.evalCoeffs as x)) b,
        BitVec.xor_assoc b (rustGf128Mul x (RoundPoly.evalCoeffs as x))
          (rustGf128Mul x (RoundPoly.evalCoeffs bs x)),
        ← BitVec.xor_assoc a b]

theorem evalCoeffs_polyScaleRust (c : RustGf128) :
    ∀ (cs : List RustGf128) (x : RustGf128),
      RoundPoly.evalCoeffs (polyScaleRust c cs) x = rustGf128Mul c (RoundPoly.evalCoeffs cs x)
  | [], _ => (rustGf128Mul_zero_right c).symm
  | d :: ds, x => by
    show rustGf128Mul c d ^^^ rustGf128Mul x (RoundPoly.evalCoeffs (polyScaleRust c ds) x) =
      rustGf128Mul c (d ^^^ rustGf128Mul x (RoundPoly.evalCoeffs ds x))
    rw [evalCoeffs_polyScaleRust c ds x, rustGf128Mul_xor_right, rustGf128Mul_left_comm]

theorem evalCoeffs_polyMulRust : ∀ (cs ds : List RustGf128) (x : RustGf128),
    RoundPoly.evalCoeffs (polyMulRust cs ds) x =
      rustGf128Mul (RoundPoly.evalCoeffs cs x) (RoundPoly.evalCoeffs ds x)
  | [], _, _ => (rustGf128Mul_zero_left _).symm
  | c :: cs, ds, x => by
    unfold polyMulRust
    rw [evalCoeffs_polyAddRust, evalCoeffs_polyScaleRust]
    show rustGf128Mul c (RoundPoly.evalCoeffs ds x) ^^^
        (0#128 ^^^ rustGf128Mul x (RoundPoly.evalCoeffs (polyMulRust cs ds) x)) =
      rustGf128Mul (c ^^^ rustGf128Mul x (RoundPoly.evalCoeffs cs x)) (RoundPoly.evalCoeffs ds x)
    rw [BitVec.zero_xor, evalCoeffs_polyMulRust cs ds x, rustGf128Mul_xor_left, rustGf128Mul_assoc]

theorem evalCoeffs_polySumRust : ∀ (n : Nat) (f : Nat → List RustGf128) (x : RustGf128),
    RoundPoly.evalCoeffs (polySumRust n f) x = rustSum n (fun i => RoundPoly.evalCoeffs (f i) x)
  | 0, _, _ => rfl
  | n + 1, f, x => by
    show RoundPoly.evalCoeffs (polyAddRust (polySumRust n f) (f n)) x =
      rustSum n (fun i => RoundPoly.evalCoeffs (f i) x) ^^^ RoundPoly.evalCoeffs (f n) x
    rw [evalCoeffs_polyAddRust, evalCoeffs_polySumRust n f x]

theorem polySumRust_length_le (B : Nat) :
    ∀ (n : Nat) (f : Nat → List RustGf128),
      (∀ i, i < n → (f i).length ≤ B) → (polySumRust n f).length ≤ B
  | 0, _, _ => Nat.zero_le B
  | n + 1, f, h => by
    simp only [polySumRust, polyAddRust_length]
    exact Nat.max_le.mpr ⟨polySumRust_length_le B n f (fun i hi => h i (by omega)), h n (by omega)⟩

theorem polyMulRust_length_le (cs ds : List RustGf128) (hds : 1 ≤ ds.length) :
    (polyMulRust cs ds).length ≤ cs.length + ds.length - 1 := by
  induction cs with
  | nil => exact Nat.zero_le _
  | cons c rest ih =>
    cases rest with
    | nil =>
      simp only [polyMulRust, polyAddRust_length, polyScaleRust, List.length_map, List.length_singleton]
      exact Nat.max_le.mpr ⟨by omega, by omega⟩
    | cons c' cs' =>
      have hStep : polyMulRust (c :: c' :: cs') ds =
          polyAddRust (polyScaleRust c ds) (0#128 :: polyMulRust (c' :: cs') ds) := rfl
      rw [hStep, polyAddRust_length, polyScaleRust, List.length_map, List.length_cons]
      simp only [List.length_cons] at ih ⊢
      exact Nat.max_le.mpr ⟨by omega, by omega⟩

theorem polyAddRust_coeffAt : ∀ (a b : List RustGf128) (k : Nat),
    coeffAt (polyAddRust a b) k = coeffAt a k ^^^ coeffAt b k
  | [], b, k => by show coeffAt b k = 0#128 ^^^ coeffAt b k; rw [BitVec.zero_xor]
  | a :: as, [], k => by
    show coeffAt (a :: as) k = coeffAt (a :: as) k ^^^ 0#128
    rw [BitVec.xor_zero]
  | _ :: _, _ :: _, 0 => rfl
  | _ :: as, _ :: bs, k + 1 => polyAddRust_coeffAt as bs k

theorem polyScaleRust_coeffAt (c : RustGf128) (cs : List RustGf128) (k : Nat) :
    coeffAt (polyScaleRust c cs) k = rustGf128Mul c (coeffAt cs k) := by
  induction cs generalizing k with
  | nil => exact (rustGf128Mul_zero_right c).symm
  | cons d ds ih =>
    cases k with
    | zero => simp only [polyScaleRust, List.map_cons, coeffAt]
    | succ k' =>
      simp only [polyScaleRust, List.map_cons, coeffAt]
      exact ih k'

theorem polySumRust_coeffAt : ∀ (n : Nat) (f : Nat → List RustGf128) (k : Nat),
    coeffAt (polySumRust n f) k = rustSum n (fun i => coeffAt (f i) k)
  | 0, _, _ => rfl
  | n + 1, f, k => by
    show coeffAt (polyAddRust (polySumRust n f) (f n)) k =
      rustSum n (fun i => coeffAt (f i) k) ^^^ coeffAt (f n) k
    rw [polyAddRust_coeffAt, polySumRust_coeffAt n f k]

theorem rustSum_succ_head (n : Nat) (f : Nat → RustGf128) :
    rustSum (n + 1) f = f 0 ^^^ rustSum n (fun u => f (u + 1)) := by
  induction n with
  | zero => show (0#128 ^^^ f 0) = f 0 ^^^ 0#128; rw [BitVec.zero_xor, BitVec.xor_zero]
  | succ n ih =>
    show (rustSum (n + 1) f) ^^^ f (n + 1) = f 0 ^^^ (rustSum n (fun u => f (u + 1)) ^^^ f (n + 1))
    rw [ih, BitVec.xor_assoc]

theorem polyMulRust_coeffAt (cs ds : List RustGf128) (k : Nat) :
    coeffAt (polyMulRust cs ds) k =
      rustSum (k + 1) (fun u => rustGf128Mul (coeffAt cs u) (coeffAt ds (k - u))) := by
  induction cs generalizing k with
  | nil =>
    have hZero : rustSum (k + 1) (fun _ => 0#128) = 0#128 := by
      induction k with
      | zero => rfl
      | succ k ih => show rustSum (k + 1) _ ^^^ 0#128 = 0#128; rw [ih, BitVec.xor_zero]
    show (0#128 : RustGf128) = _
    rw [← hZero]
    apply rustSum_congr
    intro u _; exact (rustGf128Mul_zero_left _).symm
  | cons c cs ih =>
    have hStep : polyMulRust (c :: cs) ds =
        polyAddRust (polyScaleRust c ds) (0#128 :: polyMulRust cs ds) := rfl
    cases k with
    | zero =>
      rw [hStep, polyAddRust_coeffAt, polyScaleRust_coeffAt]
      simp only [coeffAt, rustSum, Nat.sub_zero]
      rw [BitVec.xor_zero, BitVec.zero_xor]
    | succ k' =>
      rw [hStep, polyAddRust_coeffAt, polyScaleRust_coeffAt]
      simp only [coeffAt]
      rw [ih k', rustSum_succ_head (k' + 1)]
      simp only [coeffAt, Nat.sub_zero, Nat.succ_sub_succ_eq_sub]

theorem coeffAt_ofFn {n : Nat} (f : Fin n → RustGf128) (k : Nat) :
    coeffAt (List.ofFn f) k = if hk : k < n then f ⟨k, hk⟩ else 0#128 := by
  induction n generalizing k with
  | zero => simp only [List.ofFn_zero, coeffAt, Nat.not_lt_zero, ↓reduceDIte]
  | succ n ih =>
    cases k with
    | zero =>
      simp only [List.ofFn_succ, coeffAt, Nat.zero_lt_succ, ↓reduceDIte]
      rfl
    | succ k' =>
      simp only [List.ofFn_succ, coeffAt, ih (fun i : Fin n => f i.succ) k']
      by_cases hk : k' < n
      · have hk1 : k' + 1 < n + 1 := Nat.succ_lt_succ hk
        rw [cDIte_pos hk, cDIte_pos hk1]
        rfl
      · have hk1 : ¬ (k' + 1 < n + 1) := by omega
        simp only [hk, hk1, ↓reduceDIte]

theorem rustTwoPow_mul : ∀ (i j : Nat), i + j < 128 →
    rustGf128Mul (BitVec.twoPow 128 i) (BitVec.twoPow 128 j) = BitVec.twoPow 128 (i + j)
  | 0, j, _ => by
    rw [show BitVec.twoPow 128 0 = 1#128 from by decide, Nat.zero_add, rustGf128Mul_one_left]
  | i + 1, j, hij => by
    have hi : i < 127 := by omega
    have hij' : i + j < 127 := by omega
    rw [← rustGf128MulX_twoPow_succ i hi, rustGf128MulX_eq_mul, rustGf128Mul_assoc,
        rustTwoPow_mul i j (by omega), ← rustGf128MulX_eq_mul, rustGf128MulX_twoPow_succ (i + j) hij',
        show i + j + 1 = i + 1 + j from by omega]

/-- Block `A` and `B` polynomials of degree `< 16` (`D0_BITS = 16`, `outer_mpc.rs:1703-1776`). -/
def blockPolyA (pending : List PendingAnd) (base : Nat) (lane : Fin 64) : List RustGf128 :=
  List.ofFn (fun u : Fin 16 =>
    if gateLhsBit pending (base + u.val) lane then BitVec.twoPow 128 u.val else 0#128)

def blockPolyB (pending : List PendingAnd) (base : Nat) (w : RustGf128) (lane : Fin 64) :
    List RustGf128 :=
  List.ofFn (fun k : Fin 16 =>
    if gateRhsBit pending (base + (15 - k.val)) lane then w else 0#128)

/-- Round-0 claimed degree-`≤ 30` polynomial `H_0(r_0)`: slots `s ≠ 15` hold the prover's 30
    reshared cross-terms `h0`, while slot `s = 15` (`HALF_R0`) is locked to `zMid = step0ZAcc`! -/
def round0H0Coeffs (zMid : RustGf128) (h0 : Fin 30 → RustGf128) : List RustGf128 :=
  List.ofFn (fun s : Fin 31 =>
    if hs : s.val < 15 then h0 ⟨s.val, by omega⟩
    else if _ : s.val = 15 then zMid
    else h0 ⟨s.val - 1, by omega⟩)

/-- First inner-product claim produced by Round 0 (`8 * numSuper` blocks, `outer_mpc.rs:1683-1776`). -/
def round0IpClaim (pending : List PendingAnd) (numSuper : Nat)
    (gammas : Nat → RustGf128) (h0 : Fin 30 → RustGf128)
    (r0 : RustGf128) (lane : Fin 64) : IpClaim where
  len := 8 * numSuper
  a := fun blk =>
    if blk < 8 * numSuper then
      RoundPoly.evalCoeffs (blockPolyA pending (128 * (blk / 8) + 16 * (blk % 8)) lane) r0
    else 0#128
  b := fun blk =>
    if blk < 8 * numSuper then
      RoundPoly.evalCoeffs
        (blockPolyB pending (128 * (blk / 8) + 16 * (blk % 8))
          (rustGf128Mul (gammas (blk / 8)) (BitVec.twoPow 128 (16 * (blk % 8)))) lane) r0
    else 0#128
  c := RoundPoly.evalCoeffs (round0H0Coeffs (step0ZAcc pending numSuper gammas lane) h0) r0

/-- Explicit degree-`≤ 30` (`length ≤ 31`) polynomial whose evaluation at `r0` equals
    `(round0IpClaim pending numSuper gammas h0 r0 lane).err`. -/
def round0DefectCoeffs (pending : List PendingAnd) (numSuper : Nat)
    (gammas : Nat → RustGf128) (h0 : Fin 30 → RustGf128) (lane : Fin 64) : List RustGf128 :=
  polyAddRust
    (polySumRust (8 * numSuper) (fun blk =>
      polyMulRust
        (blockPolyA pending (128 * (blk / 8) + 16 * (blk % 8)) lane)
        (blockPolyB pending (128 * (blk / 8) + 16 * (blk % 8))
          (rustGf128Mul (gammas (blk / 8)) (BitVec.twoPow 128 (16 * (blk % 8)))) lane)))
    (round0H0Coeffs (step0ZAcc pending numSuper gammas lane) h0)

/-- **Exact Round-0 Polynomial Identity (`round0IpClaim_err_eq_evalCoeffs`)**:
    1. `(round0IpClaim … r0 lane).err = RoundPoly.evalCoeffs (round0DefectCoeffs …) r0` for all `r0`,
    2. `(round0DefectCoeffs …).length ≤ 31` (degree `≤ 30 = 2 * D0_BITS - 2`),
    3. The middle `r0^15` (`HALF_R0 = 15`) coefficient of `round0DefectCoeffs` equals
       `gammaCombinedDefect pending numSuper gammas lane`, completely independent of `h0`! -/
theorem round0IpClaim_err_eq_evalCoeffs
    (pending : List PendingAnd) (numSuper : Nat)
    (gammas : Nat → RustGf128) (h0 : Fin 30 → RustGf128) (lane : Fin 64) :
    (∀ r0 : RustGf128,
      (round0IpClaim pending numSuper gammas h0 r0 lane).err =
        RoundPoly.evalCoeffs (round0DefectCoeffs pending numSuper gammas h0 lane) r0) ∧
    (round0DefectCoeffs pending numSuper gammas h0 lane).length ≤ 31 ∧
    coeffAt (round0DefectCoeffs pending numSuper gammas h0 lane) 15 =
      gammaCombinedDefect pending numSuper gammas lane := by
  refine ⟨?_, ?_, ?_⟩
  · intro r0
    unfold IpClaim.err round0IpClaim round0DefectCoeffs
    rw [evalCoeffs_polyAddRust, evalCoeffs_polySumRust]
    congr 1
    have hDotEqSum : ∀ m : Nat, m ≤ 8 * numSuper →
        rustDot m
          (fun blk => if blk < 8 * numSuper then
            RoundPoly.evalCoeffs (blockPolyA pending (128 * (blk / 8) + 16 * (blk % 8)) lane) r0 else 0#128)
          (fun blk => if blk < 8 * numSuper then
            RoundPoly.evalCoeffs (blockPolyB pending (128 * (blk / 8) + 16 * (blk % 8))
              (rustGf128Mul (gammas (blk / 8)) (BitVec.twoPow 128 (16 * (blk % 8)))) lane) r0 else 0#128) =
        rustSum m (fun blk =>
          RoundPoly.evalCoeffs
            (polyMulRust
              (blockPolyA pending (128 * (blk / 8) + 16 * (blk % 8)) lane)
              (blockPolyB pending (128 * (blk / 8) + 16 * (blk % 8))
                (rustGf128Mul (gammas (blk / 8)) (BitVec.twoPow 128 (16 * (blk % 8)))) lane)) r0) := by
      intro m hm
      induction m with
      | zero => rfl
      | succ m ih =>
        have hmLt : m < 8 * numSuper := by omega
        show rustDot m _ _ ^^^ rustGf128Mul (if m < 8 * numSuper then _ else 0#128)
            (if m < 8 * numSuper then _ else 0#128) =
          rustSum m _ ^^^ _
        rw [ih (by omega), cIte_pos hmLt, cIte_pos hmLt, ← evalCoeffs_polyMulRust]
    exact hDotEqSum (8 * numSuper) (Nat.le_refl _)
  · unfold round0DefectCoeffs
    rw [polyAddRust_length]
    have hSumLe : (polySumRust (8 * numSuper) (fun blk =>
        polyMulRust
          (blockPolyA pending (128 * (blk / 8) + 16 * (blk % 8)) lane)
          (blockPolyB pending (128 * (blk / 8) + 16 * (blk % 8))
            (rustGf128Mul (gammas (blk / 8)) (BitVec.twoPow 128 (16 * (blk % 8)))) lane))).length ≤ 31 := by
      apply polySumRust_length_le 31
      intro blk _
      have hB : 1 ≤ (blockPolyB pending (128 * (blk / 8) + 16 * (blk % 8))
          (rustGf128Mul (gammas (blk / 8)) (BitVec.twoPow 128 (16 * (blk % 8)))) lane).length := by
        simp only [blockPolyB, List.length_ofFn]
        decide
      have hMul := polyMulRust_length_le
        (blockPolyA pending (128 * (blk / 8) + 16 * (blk % 8)) lane) _ hB
      simp only [blockPolyA, blockPolyB, List.length_ofFn] at hMul
      exact hMul
    have hH0Len : (round0H0Coeffs (step0ZAcc pending numSuper gammas lane) h0).length = 31 := by
      simp only [round0H0Coeffs, List.length_ofFn]
    exact Nat.max_le.mpr ⟨hSumLe, Nat.le_of_eq hH0Len⟩
  · unfold round0DefectCoeffs
    rw [polyAddRust_coeffAt, polySumRust_coeffAt]
    have hH0Mid : coeffAt (round0H0Coeffs (step0ZAcc pending numSuper gammas lane) h0) 15 =
        step0ZAcc pending numSuper gammas lane := by
      unfold round0H0Coeffs
      rw [coeffAt_ofFn, cDIte_pos (by decide : 15 < 31)]
      simp only [Nat.lt_irrefl, ↓reduceDIte]
    rw [hH0Mid]
    have hBlkMid : ∀ blk : Nat,
        coeffAt (polyMulRust
          (blockPolyA pending (128 * (blk / 8) + 16 * (blk % 8)) lane)
          (blockPolyB pending (128 * (blk / 8) + 16 * (blk % 8))
            (rustGf128Mul (gammas (blk / 8)) (BitVec.twoPow 128 (16 * (blk % 8)))) lane)) 15 =
        rustGf128Mul (gammas (blk / 8))
          (rustSum 16 (fun u =>
            if gateLhsBit pending (128 * (blk / 8) + 16 * (blk % 8) + u) lane &&
               gateRhsBit pending (128 * (blk / 8) + 16 * (blk % 8) + u) lane then
              BitVec.twoPow 128 (16 * (blk % 8) + u)
            else 0#128)) := by
      intro blk
      rw [polyMulRust_coeffAt, rustSum_mul_left]
      apply rustSum_congr
      intro u hu
      have hSub : 15 - u < 16 := by omega
      have hSubSub : 15 - (15 - u) = u := by omega
      have hSubLt8 : blk % 8 < 8 := Nat.mod_lt blk (by decide)
      unfold blockPolyA blockPolyB
      rw [coeffAt_ofFn, coeffAt_ofFn, cDIte_pos hu, cDIte_pos hSub]
      dsimp only
      rw [hSubSub]
      cases gateLhsBit pending (128 * (blk / 8) + 16 * (blk % 8) + u) lane <;>
        cases gateRhsBit pending (128 * (blk / 8) + 16 * (blk % 8) + u) lane
      · simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
        rw [rustGf128Mul_zero_left, rustGf128Mul_zero_right]
      · simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
        rw [rustGf128Mul_zero_left, rustGf128Mul_zero_right]
      · simp only [Bool.and_false, Bool.false_eq_true, ↓reduceIte]
        rw [rustGf128Mul_zero_right, rustGf128Mul_zero_right]
      · simp only [Bool.and_self, ↓reduceIte]
        rw [rustGf128Mul_left_comm (BitVec.twoPow 128 u), rustGf128Mul_comm (BitVec.twoPow 128 u),
            rustTwoPow_mul (16 * (blk % 8)) u (by omega)]
    have hSumEq : rustSum (8 * numSuper) (fun blk =>
        coeffAt (polyMulRust
          (blockPolyA pending (128 * (blk / 8) + 16 * (blk % 8)) lane)
          (blockPolyB pending (128 * (blk / 8) + 16 * (blk % 8))
            (rustGf128Mul (gammas (blk / 8)) (BitVec.twoPow 128 (16 * (blk % 8)))) lane)) 15) =
        rustDot numSuper gammas (fun q => superBlockAnd pending q lane) := by
      have hRewrite : rustSum (8 * numSuper) (fun blk =>
          coeffAt (polyMulRust
            (blockPolyA pending (128 * (blk / 8) + 16 * (blk % 8)) lane)
            (blockPolyB pending (128 * (blk / 8) + 16 * (blk % 8))
              (rustGf128Mul (gammas (blk / 8)) (BitVec.twoPow 128 (16 * (blk % 8)))) lane)) 15) =
          rustSum (numSuper * 8) (fun blk =>
            rustGf128Mul (gammas (blk / 8))
              (rustSum 16 (fun u =>
                if gateLhsBit pending (128 * (blk / 8) + 16 * (blk % 8) + u) lane &&
                   gateRhsBit pending (128 * (blk / 8) + 16 * (blk % 8) + u) lane then
                  BitVec.twoPow 128 (16 * (blk % 8) + u)
                else 0#128))) := by
        rw [Nat.mul_comm 8 numSuper]
        exact rustSum_congr (numSuper * 8) (fun blk _ => hBlkMid blk)
      rw [hRewrite, rustSum_blocks numSuper 8]
      have hDotAsSum : ∀ m : Nat,
          rustDot m gammas (fun q => superBlockAnd pending q lane) =
            rustSum m (fun q => rustGf128Mul (gammas q) (superBlockAnd pending q lane)) := by
        intro m
        induction m with
        | zero => rfl
        | succ m ih => show rustDot m _ _ ^^^ _ = rustSum m _ ^^^ _; rw [ih]
      rw [hDotAsSum]
      apply rustSum_congr
      intro q _
      have hSuperSplit : superBlockAnd pending q lane =
          rustSum 8 (fun sub => rustSum 16 (fun u =>
            if gateLhsBit pending (128 * q + (16 * sub + u)) lane &&
               gateRhsBit pending (128 * q + (16 * sub + u)) lane then
              BitVec.twoPow 128 (16 * sub + u)
            else 0#128)) :=
        rustSum_blocks 8 16 (fun k =>
          if gateLhsBit pending (128 * q + k) lane && gateRhsBit pending (128 * q + k) lane then
            BitVec.twoPow 128 k
          else 0#128)
      rw [hSuperSplit, rustSum_mul_left]
      apply rustSum_congr
      intro sub hSub
      have hDiv : (8 * q + sub) / 8 = q := by omega
      have hMod : (8 * q + sub) % 8 = sub := by omega
      rw [hDiv, hMod]
      apply congrArg (rustGf128Mul (gammas q))
      apply rustSum_congr
      intro u _
      rw [Nat.add_assoc (128 * q) (16 * sub) u]
    rw [hSumEq]
    unfold step0ZAcc gammaCombinedDefect superBlockDefect
    have hXorDot : ∀ m : Nat,
        rustDot m gammas (fun q => superBlockAnd pending q lane) ^^^
          rustDot m gammas (fun q => superBlockZ pending q lane) =
        rustDot m gammas (fun q => superBlockAnd pending q lane ^^^ superBlockZ pending q lane) := by
      intro m
      induction m with
      | zero => simp only [rustDot]; decide
      | succ m ih =>
        let A := rustDot m gammas (fun q => superBlockAnd pending q lane)
        let B := rustDot m gammas (fun q => superBlockZ pending q lane)
        let X := rustGf128Mul (gammas m) (superBlockAnd pending m lane)
        let Y := rustGf128Mul (gammas m) (superBlockZ pending m lane)
        show (A ^^^ X) ^^^ (B ^^^ Y) =
          rustDot m gammas (fun q => superBlockAnd pending q lane ^^^ superBlockZ pending q lane) ^^^
            rustGf128Mul (gammas m) (superBlockAnd pending m lane ^^^ superBlockZ pending m lane)
        rw [rustGf128Mul_xor_right, ← ih]
        show (A ^^^ X) ^^^ (B ^^^ Y) = (A ^^^ B) ^^^ (X ^^^ Y)
        rw [BitVec.xor_assoc A X (B ^^^ Y), ← BitVec.xor_assoc X B Y,
            BitVec.xor_comm X B, BitVec.xor_assoc B X Y, ← BitVec.xor_assoc A B (X ^^^ Y)]
    exact hXorDot numSuper

/-- **Round-0 Soundness (`round0_false_gamma_survives_at_most_30_coins`)**:
    Whenever `gammaCombinedDefect pending numSuper gammas lane ≠ 0#128`, for ANY maliciously chosen
    reshared cross-terms `h0 : Fin 30 → RustGf128` and ANY duplicate-free `S : List RustGf128`,
    at most `30` (`2 * D0_BITS - 2`) challenges `r0 ∈ S` make `(round0IpClaim … r0 lane).err = 0#128`! -/
theorem round0_false_gamma_survives_at_most_30_coins
    (pending : List PendingAnd) (numSuper : Nat)
    (gammas : Nat → RustGf128) (h0 : Fin 30 → RustGf128) (lane : Fin 64)
    (hGammaNe : gammaCombinedDefect pending numSuper gammas lane ≠ 0#128)
    (S : List RustGf128) (hS : S.Nodup) :
    (S.filter (fun r0 =>
      decide ((round0IpClaim pending numSuper gammas h0 r0 lane).err = 0#128))).length ≤ 30 := by
  have ⟨hEval, hLen, hMid⟩ := round0IpClaim_err_eq_evalCoeffs pending numSuper gammas h0 lane
  have hMidNe : coeffAt (round0DefectCoeffs pending numSuper gammas h0 lane) 15 ≠ 0#128 := by
    rw [hMid]; exact hGammaNe
  have hCount := rustGf128_roots_le_of_coeffAt_nonzero 30
    (round0DefectCoeffs pending numSuper gammas h0 lane) 15 S hS hLen (by decide) hMidNe
  have hPred : (fun r0 =>
      decide ((round0IpClaim pending numSuper gammas h0 r0 lane).err = 0#128)) =
      (fun r0 => decide (RoundPoly.evalCoeffs
        (round0DefectCoeffs pending numSuper gammas h0 lane) r0 = CommRingOps.zero)) := by
    funext r0; rw [hEval r0]; rfl
  rw [hPred]; exact hCount

/-- `#tooth` Mutant: if slot `s = 15` (`HALF_R0`) were prover-supplied like `h0` instead of locked
    to `step0ZAcc`, a cheating prover sets `cMid := superBlockAnd` and cancels a faulty `AND` gate
    on EVERY challenge `r0`! -/
def round0IpClaimUnlockedMid (pending : List PendingAnd) (numSuper : Nat)
    (gammas : Nat → RustGf128) (cMid : RustGf128) (h0 : Fin 30 → RustGf128)
    (r0 : RustGf128) (lane : Fin 64) : IpClaim :=
  { round0IpClaim pending numSuper gammas h0 r0 lane with
    c := RoundPoly.evalCoeffs (round0H0Coeffs cMid h0) r0 }

theorem tooth_round0_unlocked_mid_forges_every_coin :
    ∃ (pending : List PendingAnd) (gammas : Nat → RustGf128)
      (cMid : RustGf128) (h0 : Fin 30 → RustGf128),
      gammaCombinedDefect pending 1 gammas 0 ≠ 0#128 ∧
      ∀ r0 : RustGf128,
        (round0IpClaimUnlockedMid pending 1 gammas cMid h0 r0 0).err = 0#128 := by
  let zeroSh : RssWord64Shares3 := ⟨0, 0, 0⟩
  let onesSh : RssWord64Shares3 := ⟨0xFFFFFFFFFFFFFFFF, 0, 0⟩
  let pending : List PendingAnd := [⟨zeroSh, zeroSh, onesSh⟩]
  let gammas : Nat → RustGf128 := fun _ => 1#128
  refine ⟨pending, gammas, 0#128, fun _ => 0#128, ?_, ?_⟩
  · have hFault : gateErrBit pending 0 0 = true := by decide
    have hSuper := (superBlockDefect_ne_zero_of_gateErr pending 1 0 0 (by decide) hFault).2
    show (0#128 ^^^ rustGf128Mul 1#128 (superBlockDefect pending 0 0)) ≠ 0#128
    rw [BitVec.zero_xor, rustGf128Mul_one_left]
    exact hSuper
  · intro r0
    unfold IpClaim.err round0IpClaimUnlockedMid round0IpClaim
    have hA0 : ∀ blk < 8, blockPolyA pending (128 * (blk / 8) + 16 * (blk % 8)) 0 =
        List.replicate 16 0#128 := by
      intro blk hBlk
      apply List.ext_getElem?
      intro u
      simp only [blockPolyA, List.getElem?_ofFn, List.getElem?_replicate]
      by_cases hu : u < 16
      · simp only [hu, ↓reduceDIte, ↓reduceIte]
        have hFalse : gateLhsBit pending (128 * (blk / 8) + 16 * (blk % 8) + u) 0 = false := by
          unfold gateLhsBit pending
          cases hd : 128 * (blk / 8) + 16 * (blk % 8) + u with
          | zero => decide
          | succ _ => rfl
        rw [hFalse]; rfl
      · simp only [hu, ↓reduceDIte, ↓reduceIte]
    have hEvalZero : ∀ n, RoundPoly.evalCoeffs (List.replicate n (0#128 : RustGf128)) r0 = 0#128 := by
      intro n; induction n with
      | zero => rfl
      | succ n ih =>
        show 0#128 ^^^ rustGf128Mul r0 _ = 0#128
        rw [ih, rustGf128Mul_zero_right, BitVec.xor_zero]
    have hDot0 : ∀ m ≤ 8, rustDot m
        (fun blk => if blk < 8 then RoundPoly.evalCoeffs (blockPolyA pending (128 * (blk / 8) + 16 * (blk % 8)) 0) r0 else 0#128)
        (fun blk => if blk < 8 then RoundPoly.evalCoeffs (blockPolyB pending (128 * (blk / 8) + 16 * (blk % 8))
          (rustGf128Mul (gammas (blk / 8)) (BitVec.twoPow 128 (16 * (blk % 8)))) 0) r0 else 0#128) = 0#128 := by
      intro m hm; induction m with
      | zero => rfl
      | succ m ih =>
        have hmLt : m < 8 := by omega
        show rustDot m _ _ ^^^ rustGf128Mul (if m < 8 then _ else 0#128) _ = 0#128
        rw [ih (by omega), cIte_pos hmLt, hA0 m hmLt, hEvalZero 16,
            rustGf128Mul_zero_left, BitVec.xor_zero]
    have hH0Zero : round0H0Coeffs 0#128 (fun _ => 0#128) = List.replicate 31 0#128 := by
      apply List.ext_getElem?; intro s
      simp only [round0H0Coeffs, List.getElem?_ofFn, List.getElem?_replicate]
      by_cases hs : s < 31
      · simp only [hs, ↓reduceDIte, ↓reduceIte]
        by_cases hs15 : s < 15
        · simp only [hs15, ↓reduceDIte]
        · by_cases hsEq : s = 15 <;> simp only [hs15, hsEq, Nat.lt_irrefl, ↓reduceDIte]
      · simp only [hs, ↓reduceDIte, ↓reduceIte]
    dsimp only
    rw [hDot0 8 (Nat.le_refl 8), hH0Zero, hEvalZero 31, BitVec.xor_zero]

#tooth_pair Qsag.MigrationExecution.round0_false_gamma_survives_at_most_30_coins vs
  Qsag.MigrationExecution.tooth_round0_unlocked_mid_forges_every_coin

/-- Round-0 `FlushClaims` for both lockstep instances `t ∈ {0, 1}` across all 64 lanes. -/
def round0FlushClaims (pending : List PendingAnd) (numSuper : Nat)
    (gammas : Nat → RustGf128) (h0 : Fin 2 → Fin 64 → Fin 30 → RustGf128)
    (r0 : CoinPair) : FlushClaims :=
  fun t lane => round0IpClaim pending numSuper gammas (h0 t lane) (coinAt r0 t) lane

theorem wireBit_true_of_finishWithoutCheck (st : GateState) (lane : Fin 64)
    (ho : finishWithoutCheck st = .accepted) :
    match st.wires with | out :: _ => wireBit out lane = true | [] => False := by
  unfold finishWithoutCheck at ho
  cases hw : st.wires with
  | nil => simp only [hw, reduceCtorEq] at ho
  | cons out rest =>
    simp only [hw] at ho ⊢
    cases hBeq : (out.reconstruct == 0xFFFFFFFFFFFFFFFF)
    · rw [hBeq] at ho; cases ho
    · have hEqMax : out.reconstruct = 0xFFFFFFFFFFFFFFFF := eq_of_beq hBeq
      unfold wireBit
      rw [hEqMax]
      have hAll1 : (0xFFFFFFFFFFFFFFFF : UInt64).toBitVec = BitVec.allOnes 64 := by decide
      rw [hAll1, Qsag.Constructive.getLsbD_allOnes, decide_eq_true lane.isLt]

/-- **Constructive Discharge of `hLink` (`circuit_round0_discharges_hLink`)**:
    Given 7 shared batch executions `st : Fin 7 → GateState` of a circuit `gates` sound for `relB`
    on `batches : MigrationWitnessBatches` (`MigrationBatchConsistent batches`), if every repetition
    lane opens output `true` (`finishWithoutCheck (st b) = .accepted`) and each fork's `(gammas b, r0 b)`
    is outside the `γ`-combiner + Round-0 bad sets, then `FalseRepetitionGivesFalseClaims` (`hLink`)
    holds unconditionally — discharging `hLink` in
    `migration_false_statement_faces_sacrifice_in_every_repetition`! -/
theorem circuit_round0_discharges_hLink
    (gates : List Gate) (relB : MigrationKey256 → Bool) (hCirc : CircuitSoundForRel gates relB)
    (batches : MigrationWitnessBatches)
    (st : Fin 7 → GateState) (numSuper : Fin 7 → Nat)
    (gammas : Fin 7 → Nat → RustGf128)
    (h0 : Fin 7 → Fin 2 → Fin 64 → Fin 30 → RustGf128)
    (r0 : Fin 7 → CoinPair)
    (hEval : ∀ b : Fin 7, evalGates ⟨witnessWires (batches b), []⟩ gates = some (st b))
    (hOpen : ∀ b : Fin 7, finishWithoutCheck (st b) = .accepted)
    (hCap : ∀ b : Fin 7, (st b).pending.length ≤ 128 * numSuper b)
    (hGoodGamma : ∀ (b : Fin 7) (lane : Fin 64),
      (∃ q < numSuper b, superBlockDefect (st b).pending q lane ≠ 0#128) →
      gammaCombinedDefect (st b).pending (numSuper b) (gammas b) lane ≠ 0#128)
    (hGoodR0 : ∀ (b : Fin 7) (t : Fin 2) (lane : Fin 64),
      gammaCombinedDefect (st b).pending (numSuper b) (gammas b) lane ≠ 0#128 →
      (round0IpClaim (st b).pending (numSuper b) (gammas b) (h0 b t lane)
        (coinAt (r0 b) t) lane).err ≠ 0#128) :
    FalseRepetitionGivesFalseClaims batches (fun k => relB k = true)
      (fun b => round0FlushClaims (st b).pending (numSuper b) (gammas b) (h0 b) (r0 b)) := by
  intro rep hNotRel
  let b := repetitionFork rep
  let lane := repetitionLane rep
  have hRelFalse : relB (extractRepetitionWitness (batches b) lane.val) = false := by
    cases h : relB (extractRepetitionWitness (batches b) lane.val)
    · rfl
    · exact absurd h hNotRel
  have hWireTrue := wireBit_true_of_finishWithoutCheck (st b) lane (hOpen b)
  obtain ⟨idx, hIdxLt, hIdxErr⟩ := false_witness_implies_pending_and_fault gates relB hCirc
    (batches b) lane hRelFalse (st b) (hEval b) hWireTrue
  have hGateErr : gateErrBit (st b).pending idx lane = true := by
    unfold gateErrBit gateOutBit gateLhsBit gateRhsBit
    cases hp : (st b).pending[idx]? with
    | none => rw [hp] at hIdxErr; cases hIdxErr
    | some t =>
      rw [hp] at hIdxErr
      exact Option.some.inj hIdxErr
  have hSuper := superBlockDefect_ne_zero_of_gateErr (st b).pending (numSuper b) idx lane
    (Nat.lt_of_lt_of_le hIdxLt (hCap b)) hGateErr
  have hGam := hGoodGamma b lane ⟨idx / 128, hSuper.1, hSuper.2⟩
  exact ⟨hGoodR0 b 0 lane hGam, hGoodR0 b 1 lane hGam⟩

/-- Adaptive prover strategy for Round 0 + `r` binary folds + base sacrifice (`0` `@[expose]`). -/
structure Round0FlushProver (r : Nat) where
  h0 : Fin 2 → Fin 64 → Fin 30 → RustGf128
  afterR0 : CoinPair → FlushProver r

def round0FlushAccepts (r : Nat) (pending : List PendingAnd) (numSuper : Nat)
    (gammas : Nat → RustGf128) (p : Round0FlushProver r) : List CoinPair → Bool
  | [] => false
  | r0 :: rest =>
    flushAccepts r (p.afterR0 r0) (round0FlushClaims pending numSuper gammas p.h0 r0) rest

/-- Single-instance bad-coin count across Round 0 (`30`) + `r` binary folds (`2r`) + base (`2`).
    At `r = 11` (`2048` blocks of `D0_BITS = 16`) the numerator is `30 + 22 + 2 = 54`. -/
def round0SacrificeBadBound (n nb r : Nat) : Nat :=
  30 * (n ^ r * nb) + n * sacrificeBadCoinBound n nb r

theorem round0Flush_false_gamma_accepting_coins_bound
    (S Sb : List RustGf128) (hS : S.Nodup) (hSb : Sb.Nodup) (r : Nat)
    (pending : List PendingAnd) (numSuper : Nat) (gammas : Nat → RustGf128)
    (p : Round0FlushProver r) (lane : Fin 64)
    (hGammaNe : gammaCombinedDefect pending numSuper gammas lane ≠ 0#128) :
    ((flushCoinVectors S Sb (r + 1)).filter
      (round0FlushAccepts r pending numSuper gammas p)).length ≤
      round0SacrificeBadBound S.length Sb.length r *
        round0SacrificeBadBound S.length Sb.length r := by
  have hCount : ((flushCoinVectors S Sb (r + 1)).filter
      (round0FlushAccepts r pending numSuper gammas p)).length =
      (S.map (fun a => (S.map (fun b =>
        flushAccepting S Sb r (p.afterR0 (a, b))
          (round0FlushClaims pending numSuper gammas p.h0 (a, b)))).sum)).sum := by
    show (((coinPairs S).flatMap (fun r0 => (flushCoinVectors S Sb r).map (fun rest => r0 :: rest))).filter
      (round0FlushAccepts r pending numSuper gammas p)).length = _
    rw [filter_flatMap_length]
    have hMapEq : ((coinPairs S).map (fun r0 =>
        (((flushCoinVectors S Sb r).map (fun rest => r0 :: rest)).filter
          (round0FlushAccepts r pending numSuper gammas p)).length)) =
        ((coinPairs S).map (fun r0 =>
          flushAccepting S Sb r (p.afterR0 r0)
            (round0FlushClaims pending numSuper gammas p.h0 r0))) := by
      apply List.map_congr_left
      intro r0 _
      rw [filter_map_length, flushAccepting_eq_filter]
      rfl
    rw [hMapEq]
    exact sum_map_pairs (fun r0 =>
      flushAccepting S Sb r (p.afterR0 r0)
        (round0FlushClaims pending numSuper gammas p.h0 r0)) S S
  let w0 : RustGf128 → Nat := fun a =>
    laneWeight S.length Sb.length
      (decide ((round0IpClaim pending numSuper gammas (p.h0 0 lane) a lane).err ≠ 0#128)) r
  let w1 : RustGf128 → Nat := fun b =>
    laneWeight S.length Sb.length
      (decide ((round0IpClaim pending numSuper gammas (p.h0 1 lane) b lane).err ≠ 0#128)) r
  have hCell : ∀ a b, flushAccepting S Sb r (p.afterR0 (a, b))
      (round0FlushClaims pending numSuper gammas p.h0 (a, b)) ≤ w0 a * w1 b := by
    intro a b
    exact flushAccepting_le_weights S Sb hS hSb lane r (p.afterR0 (a, b))
      (round0FlushClaims pending numSuper gammas p.h0 (a, b))
      (decide ((round0IpClaim pending numSuper gammas (p.h0 0 lane) a lane).err ≠ 0#128))
      (decide ((round0IpClaim pending numSuper gammas (p.h0 1 lane) b lane).err ≠ 0#128))
      (fun h => of_decide_eq_true h) (fun h => of_decide_eq_true h)
  have hW0 : (S.map w0).sum ≤ round0SacrificeBadBound S.length Sb.length r := by
    have hSplit := sum_map_le_cases
      (fun a => decide ((round0IpClaim pending numSuper gammas (p.h0 0 lane) a lane).err = 0#128))
      w0 (S.length ^ r * Sb.length) (sacrificeBadCoinBound S.length Sb.length r)
      (fun a hb => by
        dsimp only [w0]
        rw [decide_eq_false (fun hne => hne (of_decide_eq_true hb))]
        exact Nat.le_refl _)
      (fun a hg => by
        dsimp only [w0]
        rw [decide_eq_true (of_decide_eq_false hg)]
        exact Nat.le_refl _) S
    have hBad := round0_false_gamma_survives_at_most_30_coins pending numSuper gammas
      (p.h0 0 lane) lane hGammaNe S hS
    have hMul := Nat.mul_le_mul_right (S.length ^ r * Sb.length) hBad
    unfold round0SacrificeBadBound
    omega
  have hW1 : (S.map w1).sum ≤ round0SacrificeBadBound S.length Sb.length r := by
    have hSplit := sum_map_le_cases
      (fun b => decide ((round0IpClaim pending numSuper gammas (p.h0 1 lane) b lane).err = 0#128))
      w1 (S.length ^ r * Sb.length) (sacrificeBadCoinBound S.length Sb.length r)
      (fun b hb => by
        dsimp only [w1]
        rw [decide_eq_false (fun hne => hne (of_decide_eq_true hb))]
        exact Nat.le_refl _)
      (fun b hg => by
        dsimp only [w1]
        rw [decide_eq_true (of_decide_eq_false hg)]
        exact Nat.le_refl _) S
    have hBad := round0_false_gamma_survives_at_most_30_coins pending numSuper gammas
      (p.h0 1 lane) lane hGammaNe S hS
    have hMul := Nat.mul_le_mul_right (S.length ^ r * Sb.length) hBad
    unfold round0SacrificeBadBound
    omega
  rw [hCount]
  calc (S.map (fun a => (S.map (fun b =>
          flushAccepting S Sb r (p.afterR0 (a, b))
            (round0FlushClaims pending numSuper gammas p.h0 (a, b)))).sum)).sum
      ≤ (S.map (fun a => (S.map (fun b => w0 a * w1 b)).sum)).sum :=
        sum_map_le_sum_map _ _ (fun a => sum_map_le_sum_map _ _ (fun b => hCell a b) S) S
    _ = (S.map w0).sum * (S.map w1).sum := sum_sum_mul w0 w1 S S
    _ ≤ round0SacrificeBadBound S.length Sb.length r *
          round0SacrificeBadBound S.length Sb.length r := Nat.mul_le_mul hW0 hW1

/-- The `D0_BITS = 16` round-0 geometry modelled above (128-gate super-blocks, one degree-30
    round 0, then `r` binary folds): at `r = 11` (`32768 / 16 = 2048 = 2^11` blocks) the
    single-instance numerator is `30 + 2 · 11 + 2 = 54`, and the two-instance bound is below
    `2^-244` up to `r ≤ 13`. This is not the geometry of the current `outer_mpc.rs`
    (`BIT_CHECK_NUMERATOR = 63`); see `rust_bit_check_numerator_63_bound` for that one. -/
theorem d16_round0_sacrifice_bit_check_54_bound :
    round0SacrificeBadBound (2 ^ 128) (2 ^ 128 - 1) 11 * (2 ^ 128 - 1) ≤
      54 * ((2 ^ 128) ^ 12 * (2 ^ 128 - 1)) ∧
    ∀ r, r ≤ 13 →
      round0SacrificeBadBound (2 ^ 128) (2 ^ 128 - 1) r *
        round0SacrificeBadBound (2 ^ 128) (2 ^ 128 - 1) r * 2 ^ 244 ≤
      ((2 ^ 128) ^ (r + 1) * (2 ^ 128 - 1)) * ((2 ^ 128) ^ (r + 1) * (2 ^ 128 - 1)) := by
  decide +kernel

/-! ### Staged reductions ahead of the halving rounds: the `outer_mpc.rs` geometry (numerator 63)

`verify_pending_bits_slice` no longer packs 16-gate blocks into a degree-30 round 0. It runs,
per instance: a weighted embedding with `6` word-offset challenges and one group challenge
(`BIT_TENSOR_BITS + 1 = 7` linear stages), `6` packed ternary sumcheck rounds (degree `3` in the
round coin), then `log2 MAX_BIT_GROUPS + log2 BIT_LANES = 12 + 6 = 18` halving rounds and the
base sacrifice. `BIT_CHECK_NUMERATOR = 7 + 3 · 6 + 2 · 18 + 2 = 63`.

What is proved for this geometry. The `18` halving rounds and the base case are `foldRound` and
`baseAccepts` above. The `13` stages before them are a parameter: `StagesSound` asks, for each
stage, that at most `d` coins turn a false claim into a true one whatever message the prover
sent before the coin. Under that hypothesis `staged_sacrifice_false_claim_accepting_coins_bound`
counts the accepting coin vectors of any adaptive prover, and
`rust_bit_check_numerator_63_bound` evaluates the count at the Rust stage list and coin sets.

What is not proved. `StagesSound` is not derived from the Rust weighted embedding and ternary
sumcheck (their claim types, the tensor weights and the round polynomials are not modelled),
the group challenge is counted as one coin although Rust draws one coin per group, and the
count is for one instance and one lane: the 64-lane two-instance lockstep flush and the
438-repetition ceremony bound above remain theorems about the `D0_BITS = 16` model. -/

/-- Adaptive prover for a list of reduction stages followed by a tail protocol with prover type
    `T`: one message per stage, the rest of the strategy a function of that stage's coin. -/
@[expose] def StagedProver (Msg T : Type) : List Nat → Type
  | [] => T
  | _ :: ds => Msg × (RustGf128 → StagedProver Msg T ds)

/-- Verdict on one coin vector: one coin per stage, then the tail's coins. `stage k` is the
    stage with `k` stages still to follow. A coin vector that is too short rejects. -/
def stagedAccepts {Cl Msg T : Type} (stage : Nat → Cl → Msg → RustGf128 → Cl)
    (tail : T → Cl → List RustGf128 → Bool) :
    (ds : List Nat) → StagedProver Msg T ds → Cl → List RustGf128 → Bool
  | [], p, s, coins => tail p s coins
  | _ :: _, _, _, [] => false
  | _ :: ds, p, s, c :: coins =>
    stagedAccepts stage tail ds (p.2 c) (stage ds.length s p.1 c) coins

/-- All coin vectors: one coin from `S` per stage, then a tail vector. -/
def stagedCoinVectors (S : List RustGf128) (tailVecs : List (List RustGf128)) :
    List Nat → List (List RustGf128)
  | [] => tailVecs
  | _ :: ds => S.flatMap (fun c => (stagedCoinVectors S tailVecs ds).map (fun rest => c :: rest))

/-- Per-stage soundness: with `k` stages to follow and degree bound `d`, at most `d` coins of
    `S` map a false claim to a true one, for every prover message. -/
def StagesSound {Cl Msg : Type} (S : List RustGf128) (stage : Nat → Cl → Msg → RustGf128 → Cl)
    (isFalse : Cl → Bool) : List Nat → Prop
  | [] => True
  | d :: ds =>
    (∀ (s : Cl) (m : Msg), isFalse s = true →
      (S.filter (fun c => !isFalse (stage ds.length s m c))).length ≤ d) ∧
    StagesSound S stage isFalse ds

/-- Bad-coin count of the staged protocol: `n` coins per stage, `T` tail vectors of which at
    most `B` accept a false claim. Divided by `n ^ ds.length * T` it is `Σ d / n + B / T`. -/
def stagedBadCoinBound (n T B : Nat) : List Nat → Nat
  | [] => B
  | d :: ds => d * (n ^ ds.length * T) + n * stagedBadCoinBound n T B ds

private theorem flatMap_map_cons_length {α : Type} (V : List (List α)) : ∀ S : List α,
    (S.flatMap (fun c => V.map (fun rest => c :: rest))).length = S.length * V.length
  | [] => by rw [List.flatMap_nil, List.length_nil, List.length_nil, Nat.zero_mul]
  | x :: xs => by
    rw [List.flatMap_cons, List.length_append, List.length_map, flatMap_map_cons_length V xs,
      List.length_cons, Nat.add_mul, Nat.one_mul, Nat.add_comm]

theorem stagedCoinVectors_length (S : List RustGf128) (tailVecs : List (List RustGf128)) :
    ∀ ds : List Nat,
      (stagedCoinVectors S tailVecs ds).length = S.length ^ ds.length * tailVecs.length
  | [] => by
    show tailVecs.length = S.length ^ 0 * tailVecs.length
    rw [Nat.pow_zero, Nat.one_mul]
  | _ :: ds => by
    show (S.flatMap (fun c => (stagedCoinVectors S tailVecs ds).map (fun rest => c :: rest))).length =
      S.length ^ (ds.length + 1) * tailVecs.length
    rw [flatMap_map_cons_length, stagedCoinVectors_length S tailVecs ds, Nat.pow_succ,
      Nat.mul_comm (S.length ^ ds.length) S.length, Nat.mul_assoc]

/-- **Staged reduction count.** If every stage is sound and the tail accepts a false claim on
    at most `B` of its coin vectors, an adaptive prover starting from a false claim is accepted
    on at most `stagedBadCoinBound` coin vectors. -/
theorem staged_false_claim_accepting_coins_bound {Cl Msg T : Type}
    (S : List RustGf128) (tailVecs : List (List RustGf128))
    (stage : Nat → Cl → Msg → RustGf128 → Cl) (isFalse : Cl → Bool)
    (tail : T → Cl → List RustGf128 → Bool) (B : Nat)
    (hTail : ∀ (p : T) (s : Cl), isFalse s = true → (tailVecs.filter (tail p s)).length ≤ B) :
    ∀ (ds : List Nat), StagesSound S stage isFalse ds →
      ∀ (p : StagedProver Msg T ds) (s : Cl), isFalse s = true →
        ((stagedCoinVectors S tailVecs ds).filter (stagedAccepts stage tail ds p s)).length ≤
          stagedBadCoinBound S.length tailVecs.length B ds
  | [], _, p, s, hs => hTail p s hs
  | d :: ds, hSound, p, s, hs => by
    obtain ⟨hHead, hRest⟩ := hSound
    show ((S.flatMap (fun c => (stagedCoinVectors S tailVecs ds).map (fun rest => c :: rest))).filter
        (stagedAccepts stage tail (d :: ds) p s)).length ≤
      d * (S.length ^ ds.length * tailVecs.length) +
        S.length * stagedBadCoinBound S.length tailVecs.length B ds
    rw [filter_flatMap_length]
    have hMapEq : (S.map (fun c =>
        (((stagedCoinVectors S tailVecs ds).map (fun rest => c :: rest)).filter
          (stagedAccepts stage tail (d :: ds) p s)).length)) =
        (S.map (fun c =>
          ((stagedCoinVectors S tailVecs ds).filter
            (stagedAccepts stage tail ds (p.2 c) (stage ds.length s p.1 c))).length)) := by
      apply List.map_congr_left
      intro c _
      rw [filter_map_length]
      rfl
    rw [hMapEq]
    have hSplit := sum_map_le_cases (fun c => !isFalse (stage ds.length s p.1 c))
      (fun c => ((stagedCoinVectors S tailVecs ds).filter
        (stagedAccepts stage tail ds (p.2 c) (stage ds.length s p.1 c))).length)
      (S.length ^ ds.length * tailVecs.length) (stagedBadCoinBound S.length tailVecs.length B ds)
      (fun c _ => by
        rw [← stagedCoinVectors_length S tailVecs ds]
        exact List.length_filter_le _ _)
      (fun c hc => by
        have hc' : (!isFalse (stage ds.length s p.1 c)) = false := hc
        have hStill : isFalse (stage ds.length s p.1 c) = true := by
          cases h : isFalse (stage ds.length s p.1 c) with
          | true => rfl
          | false => rw [h] at hc'; cases hc'
        exact staged_false_claim_accepting_coins_bound S tailVecs stage isFalse tail B hTail ds
          hRest (p.2 c) (stage ds.length s p.1 c) hStill) S
    have hBad := hHead s p.1 hs
    have hMul := Nat.mul_le_mul_right (S.length ^ ds.length * tailVecs.length) hBad
    exact Nat.le_trans hSplit (Nat.add_le_add_right hMul _)

/-- **Staged reductions followed by `r` halving rounds and the base sacrifice.** `embed` reads
    the inner-product claim the last stage hands to the halving rounds. -/
theorem staged_sacrifice_false_claim_accepting_coins_bound {Cl Msg : Type}
    (S Sb : List RustGf128) (hS : S.Nodup) (hSb : Sb.Nodup) (r : Nat)
    (stage : Nat → Cl → Msg → RustGf128 → Cl) (embed : Cl → IpClaim) (ds : List Nat)
    (hStages : StagesSound S stage (fun s => decide ((embed s).err ≠ 0#128)) ds)
    (p : StagedProver Msg (FoldProver r) ds) (s : Cl) (hErr : (embed s).err ≠ 0#128) :
    ((stagedCoinVectors S (coinVectors S Sb r) ds).filter
      (stagedAccepts stage (fun q c coins => sacrificeAccepts r q (embed c) coins) ds p s)).length ≤
      stagedBadCoinBound S.length (S.length ^ r * Sb.length)
        (sacrificeBadCoinBound S.length Sb.length r) ds := by
  have h := staged_false_claim_accepting_coins_bound S (coinVectors S Sb r) stage
    (fun s => decide ((embed s).err ≠ 0#128))
    (fun q c coins => sacrificeAccepts r q (embed c) coins)
    (sacrificeBadCoinBound S.length Sb.length r)
    (fun q c hc => by
      have hq := recursive_sacrifice_false_claim_accepting_coins_bound S Sb hS hSb r q (embed c)
        (of_decide_eq_true hc)
      rw [acceptingCoins_eq_filter] at hq
      exact hq)
    ds hStages p s (decide_eq_true hErr)
  rw [coinVectors_length] at h
  exact h

/-- Stage numerators of `verify_pending_bits_slice` ahead of the halving rounds: `6` word-offset
    weights and `1` group weight (`7` linear stages), then `BIT_TENSOR_BITS = 6` ternary
    sumcheck rounds of degree `3`. -/
def rustBitCheckStageNumerators : List Nat := List.replicate 7 1 ++ List.replicate 6 3

/-- Halving rounds of a full flush: `log2 MAX_BIT_GROUPS + log2 BIT_LANES`. -/
def rustBitCheckHalvingRounds : Nat := 18

/-- **`BIT_CHECK_NUMERATOR = 63` at the Rust geometry.** `MAX_PENDING_BITS / BIT_GROUP_WORDS =
    262144 / 64 = 2^12` groups and `64 = 2^6` lanes give `18` halving rounds; the stage
    numerators sum to `7 + 18 = 25`; with fold coins over `GF(2^128)` and a nonzero base coin
    the staged count is at most `63 / (2^128 - 1)` of the coin space for one instance, and its
    square (two independent instances) is below `2^-244`. -/
theorem rust_bit_check_numerator_63_bound :
    (262144 / 64 = 2 ^ 12 ∧ 64 = 2 ^ 6 ∧ rustBitCheckHalvingRounds = 12 + 6) ∧
    rustBitCheckStageNumerators.sum + 2 * rustBitCheckHalvingRounds + 2 = 63 ∧
    stagedBadCoinBound (2 ^ 128) ((2 ^ 128) ^ rustBitCheckHalvingRounds * (2 ^ 128 - 1))
        (sacrificeBadCoinBound (2 ^ 128) (2 ^ 128 - 1) rustBitCheckHalvingRounds)
        rustBitCheckStageNumerators * (2 ^ 128 - 1) ≤
      63 * ((2 ^ 128) ^ rustBitCheckStageNumerators.length *
        ((2 ^ 128) ^ rustBitCheckHalvingRounds * (2 ^ 128 - 1))) ∧
    stagedBadCoinBound (2 ^ 128) ((2 ^ 128) ^ rustBitCheckHalvingRounds * (2 ^ 128 - 1))
        (sacrificeBadCoinBound (2 ^ 128) (2 ^ 128 - 1) rustBitCheckHalvingRounds)
        rustBitCheckStageNumerators *
      stagedBadCoinBound (2 ^ 128) ((2 ^ 128) ^ rustBitCheckHalvingRounds * (2 ^ 128 - 1))
        (sacrificeBadCoinBound (2 ^ 128) (2 ^ 128 - 1) rustBitCheckHalvingRounds)
        rustBitCheckStageNumerators * 2 ^ 244 ≤
      ((2 ^ 128) ^ rustBitCheckStageNumerators.length *
        ((2 ^ 128) ^ rustBitCheckHalvingRounds * (2 ^ 128 - 1))) *
      ((2 ^ 128) ^ rustBitCheckStageNumerators.length *
        ((2 ^ 128) ^ rustBitCheckHalvingRounds * (2 ^ 128 - 1))) := by
  decide +kernel

#verify_constructive
  stagedCoinVectors_length
  staged_false_claim_accepting_coins_bound
  staged_sacrifice_false_claim_accepting_coins_bound
  rust_bit_check_numerator_63_bound

/-- Full adaptive 7-fork ceremony prover including `γ`-combiner + Round 0 + `r` folds + base. -/
abbrev FullCeremonyCoins := Fin 7 → RustGf128 × List CoinPair
abbrev FullCeremonyProver (r : Nat) := Fin 7 → FullCeremonyCoins → Round0FlushProver r

def setFullForkCoins (coins : FullCeremonyCoins) (b : Fin 7)
    (gv : RustGf128 × List CoinPair) : FullCeremonyCoins :=
  fun b' => if b' = b then gv else coins b'

def FullForkStrategiesPrecedeOwnCoins {r : Nat} (p : FullCeremonyProver r) : Prop :=
  ∀ (b : Fin 7) (c : FullCeremonyCoins) (gv : RustGf128 × List CoinPair),
    p b (setFullForkCoins c b gv) = p b c

def fullCeremonyAccepts (r : Nat) (st : Fin 7 → GateState) (numSuper : Fin 7 → Nat)
    (otherGammas : Fin 7 → Nat → RustGf128) (qFocus : Fin 7 → Nat)
    (p : FullCeremonyProver r) (coins : FullCeremonyCoins) : Bool :=
  finAll 7 (fun b =>
    round0FlushAccepts r (st b).pending (numSuper b)
      (setGammaAt (otherGammas b) (qFocus b) (coins b).1) (p b coins) (coins b).2)

def fullFlushCoinSpace (S Sb : List RustGf128) (r : Nat) : List (RustGf128 × List CoinPair) :=
  S.flatMap (fun g => (flushCoinVectors S Sb (r + 1)).map (fun v => (g, v)))

/-- **Unconditional 438-Repetition Circuit-to-Sacrifice Ceremony Soundness
    (`migration_unconditional_circuit_to_sacrifice_ceremony_bound`)**:
    With **ZERO unproved `hLink` hypothesis**, if `gates` is sound for `relB`, `batches` is
    consistent (`MigrationBatchConsistent batches`), `relB (extractRepetitionWitness (batches 0) 0) = false`,
    and every fork's shared trace opens `0xFFFFFFFFFFFFFFFF` (`finishWithoutCheck (st b) = .accepted`),
    then for EVERY repetition `rep : Fin 438`:
    1. `rep` evaluates the same false witness (`relB (migrationRepetitionWitness batches rep) = false`),
    2. `findFaultyGateIdx` constructively extracts a faulty `PendingAnd` gate in `(st (repetitionFork rep)).pending`,
    3. Across the full per-fork `(γ, r0, fold_1..fold_r, rb)` coin space (`r ≤ 13`), the 7-fork
       ceremony accepts on `< 2^-127` of the fork's full coin tuples (and `< 2^-244` on every
       non-cancelling `γ` coin)! -/
theorem migration_unconditional_circuit_to_sacrifice_ceremony_bound
    (gates : List Gate) (relB : MigrationKey256 → Bool) (hCirc : CircuitSoundForRel gates relB)
    (batches : MigrationWitnessBatches) (hB : MigrationBatchConsistent batches)
    (hFalse : relB (extractRepetitionWitness (batches 0) 0) = false)
    (st : Fin 7 → GateState) (numSuper : Fin 7 → Nat)
    (hEval : ∀ b : Fin 7, evalGates ⟨witnessWires (batches b), []⟩ gates = some (st b))
    (hOpen : ∀ b : Fin 7, finishWithoutCheck (st b) = .accepted)
    (hCap : ∀ b : Fin 7, (st b).pending.length ≤ 128 * numSuper b)
    (r : Nat) (hr : r ≤ 13)
    (otherGammas : Fin 7 → Nat → RustGf128)
    (p : FullCeremonyProver r) (hOwn : FullForkStrategiesPrecedeOwnCoins p) :
    ∀ (rep : Fin 438) (others : FullCeremonyCoins),
      let b := repetitionFork rep
      let lane := repetitionLane rep
      relB (migrationRepetitionWitness batches rep) = false ∧
      ∃ qStar : Nat, qStar < numSuper b ∧
        superBlockDefect (st b).pending qStar lane ≠ 0#128 ∧
        ((fullFlushCoinSpace productionFoldCoins productionBaseCoins r).filter (fun gv =>
          fullCeremonyAccepts r st numSuper otherGammas
            (fun b' => if b' = b then qStar else 0) p
            (setFullForkCoins others b gv))).length * 2 ^ 127 ≤
          (fullFlushCoinSpace productionFoldCoins productionBaseCoins r).length := by
  intro rep others b lane
  have hRepEq := migration_all_438_repetitions_same_witness batches hB rep
  have hRepFalse : relB (migrationRepetitionWitness batches rep) = false := by
    rw [hRepEq]; exact hFalse
  refine ⟨hRepFalse, ?_⟩
  have hWireTrue := wireBit_true_of_finishWithoutCheck (st b) lane (hOpen b)
  have hLaneFalse : relB (extractRepetitionWitness (batches b) lane.val) = false := hRepFalse
  obtain ⟨idx, hIdxLt, hIdxErr⟩ := false_witness_implies_pending_and_fault gates relB hCirc
    (batches b) lane hLaneFalse (st b) (hEval b) hWireTrue
  have hGateErr : gateErrBit (st b).pending idx lane = true := by
    unfold gateErrBit gateOutBit gateLhsBit gateRhsBit
    cases hp : (st b).pending[idx]? with
    | none => rw [hp] at hIdxErr; cases hIdxErr
    | some t => rw [hp] at hIdxErr; exact Option.some.inj hIdxErr
  have ⟨hqLt, hSuperNe⟩ := superBlockDefect_ne_zero_of_gateErr (st b).pending (numSuper b) idx lane
    (Nat.lt_of_lt_of_le hIdxLt (hCap b)) hGateErr
  let qStar := idx / 128
  refine ⟨qStar, hqLt, hSuperNe, ?_⟩
  let S := productionFoldCoins
  let Sb := productionBaseCoins
  let qFocus : Fin 7 → Nat := fun b' => if b' = b then qStar else 0
  have hFocusSelf : qFocus b = qStar := by simp only [qFocus, ↓reduceIte]
  let V := flushCoinVectors S Sb (r + 1)
  have hImp : ∀ g v,
      fullCeremonyAccepts r st numSuper otherGammas qFocus p (setFullForkCoins others b (g, v)) = true →
      round0FlushAccepts r (st b).pending (numSuper b)
        (setGammaAt (otherGammas b) qStar g) (p b others) v = true := by
    intro g v hv
    have hb := (finAll_eq_true_iff 7 _).mp hv b
    have hSelf : setFullForkCoins others b (g, v) b = (g, v) := by
      simp only [setFullForkCoins, ↓reduceIte]
    rw [hOwn b others (g, v), hSelf, hFocusSelf] at hb
    exact hb
  have hCountLe : ((fullFlushCoinSpace S Sb r).filter (fun gv =>
      fullCeremonyAccepts r st numSuper otherGammas qFocus p (setFullForkCoins others b gv))).length ≤
      (S.map (fun g => (V.filter (round0FlushAccepts r (st b).pending (numSuper b)
        (setGammaAt (otherGammas b) qStar g) (p b others))).length)).sum := by
    unfold fullFlushCoinSpace
    rw [filter_flatMap_length]
    apply sum_map_le_sum_map
    intro g
    rw [filter_map_length]
    exact filter_length_le_of_imp _ _ (fun v hv => hImp g v hv) V
  let T := V.length
  let B := round0SacrificeBadBound S.length Sb.length r *
             round0SacrificeBadBound S.length Sb.length r
  have hSplit := sum_map_le_cases
    (fun g => decide (gammaCombinedDefect (st b).pending (numSuper b)
      (setGammaAt (otherGammas b) qStar g) lane = 0#128))
    (fun g => (V.filter (round0FlushAccepts r (st b).pending (numSuper b)
      (setGammaAt (otherGammas b) qStar g) (p b others))).length)
    T B
    (fun g _ => List.length_filter_le _ V)
    (fun g hg => round0Flush_false_gamma_accepting_coins_bound S Sb
      productionFoldCoins_nodup productionBaseCoins_nodup r
      (st b).pending (numSuper b) (setGammaAt (otherGammas b) qStar g)
      (p b others) lane (of_decide_eq_false hg))
    S
  have hBadGamma := gammaCombinedDefect_bad_coins_le_one (st b).pending (numSuper b) qStar lane
    hqLt hSuperNe (otherGammas b) S productionFoldCoins_nodup
  have hSumLe : (S.map (fun g => (V.filter (round0FlushAccepts r (st b).pending (numSuper b)
      (setGammaAt (otherGammas b) qStar g) (p b others))).length)).sum ≤ 1 * T + S.length * B :=
    Nat.le_trans hSplit (Nat.add_le_add_right (Nat.mul_le_mul_right T hBadGamma) _)
  have hTotalLen : (fullFlushCoinSpace S Sb r).length = S.length * T :=
    flatMap_map_length V (fun g v => (g, v)) S
  have hArith : (1 * T + S.length * B) * 2 ^ 127 ≤ S.length * T := by
    dsimp only [T, B, V]
    rw [flushCoinVectors_length, productionFoldCoins_card, productionBaseCoins_card]
    have hR0 := d16_round0_sacrifice_bit_check_54_bound.2 r hr
    generalize ((2 ^ 128) ^ (r + 1) * (2 ^ 128 - 1)) * ((2 ^ 128) ^ (r + 1) * (2 ^ 128 - 1)) = M at hR0 ⊢
    generalize round0SacrificeBadBound (2 ^ 128) (2 ^ 128 - 1) r *
        round0SacrificeBadBound (2 ^ 128) (2 ^ 128 - 1) r = K at hR0 ⊢
    have h128le244 : 2 ^ 128 ≤ 2 ^ 244 :=
      Nat.pow_le_pow_right (by decide : 0 < 2) (by decide : 128 ≤ 244)
    have hB128 : K * 2 ^ 128 ≤ M := Nat.le_trans (Nat.mul_le_mul_left K h128le244) hR0
    rw [Nat.one_mul, Nat.add_mul]
    have hK2 : (2 ^ 128 * K) * 2 ^ 127 = (K * 2 ^ 128) * 2 ^ 127 := by
      rw [Nat.mul_comm (2 ^ 128) K]
    rw [hK2]
    have hHalf : M * 2 ^ 127 + (K * 2 ^ 128) * 2 ^ 127 ≤ M * 2 ^ 127 + M * 2 ^ 127 :=
      Nat.add_le_add_left (Nat.mul_le_mul_right (2 ^ 127) hB128) _
    have hDouble : M * 2 ^ 127 + M * 2 ^ 127 = 2 ^ 128 * M := by
      have h2 : (2 ^ 128 : Nat) = 2 ^ 127 + 2 ^ 127 := by
        rw [Nat.pow_succ 2 127, Nat.mul_two]
      rw [h2, Nat.add_mul, Nat.mul_comm M (2 ^ 127)]
    exact hDouble ▸ hHalf
  rw [hTotalLen]
  exact Nat.le_trans (Nat.mul_le_mul_right (2 ^ 127) (Nat.le_trans hCountLe hSumLe)) hArith

/-! ### 11B. Production `BIT_CHECK_NUMERATOR = 63` (`D0_BITS = 19` & Concrete 13-Stage `StagesSound`)
    and `FIELD_CHECK_NUMERATOR = 35` (`outer_mpc.rs:36-52, 1873-2055`) -/

/-- Production constants from `crates/qsag-migrate/src/outer_mpc.rs:36-52`. -/
def BIT_TENSOR_BITS : Nat := 6
def MAX_BIT_GROUPS_LOG2 : Nat := 12
def BIT_LANES_LOG2 : Nat := 6
def BIT_CHECK_NUMERATOR : Nat := 63
def D0_BITS_PROD : Nat := 19
def HALF_R0_PROD : Nat := 18
def DEG_R0_PROD : Nat := 36
def MAX_PENDING_FIELD_WORDS : Nat := 1024
def FIELD_CHECK_HALVING_ROUNDS : Nat := 16
def FIELD_CHECK_NUMERATOR : Nat := 35

theorem outer_mpc_ceremony_constants_exact :
    BIT_CHECK_NUMERATOR =
      7 + 3 * BIT_TENSOR_BITS + 2 * (MAX_BIT_GROUPS_LOG2 + BIT_LANES_LOG2) + 2 ∧
    BIT_CHECK_NUMERATOR = 1 + DEG_R0_PROD + 2 * MAX_BIT_GROUPS_LOG2 + 2 ∧
    BIT_CHECK_NUMERATOR = 63 ∧
    BIT_CHECK_NUMERATOR * BIT_CHECK_NUMERATOR < 4096 ∧
    FIELD_CHECK_NUMERATOR = 1 + 2 * FIELD_CHECK_HALVING_ROUNDS + 2 ∧
    FIELD_CHECK_NUMERATOR = 35 ∧
    MAX_PENDING_FIELD_WORDS * 64 = 2 ^ FIELD_CHECK_HALVING_ROUNDS := by
  decide

/-- Concrete stage claim for the 13-stage weighted-embedding (`7` linear stages) + packed ternary
    sumcheck (`6` degree-3 stages) ahead of the `18` halving rounds (`outer_mpc.rs:36-39`). -/
structure RustBitStageClaim where
  targetErr : RustGf128
  c0 : RustGf128

/-- Prover message in a weighted-embedding or degree-3 ternary sumcheck stage. -/
structure RustBitStageMsg where
  t0 : RustGf128
  t2 : RustGf128
  t3 : RustGf128

/-- Embeds the post-sumcheck claim as a length-1 `IpClaim` with `(rustBitStageEmbed cl).err = cl.targetErr`. -/
def rustBitStageEmbed (cl : RustBitStageClaim) : IpClaim where
  len := 1
  a := fun k => if k = 0 then cl.targetErr ^^^ cl.c0 else 0#128
  b := fun k => if k = 0 then 1#128 else 0#128
  c := cl.c0

theorem rustBitStageEmbed_err (cl : RustBitStageClaim) :
    (rustBitStageEmbed cl).err = cl.targetErr := by
  unfold IpClaim.err rustBitStageEmbed
  show (0#128 ^^^ rustGf128Mul (cl.targetErr ^^^ cl.c0) 1#128) ^^^ cl.c0 = cl.targetErr
  rw [BitVec.zero_xor, rustGf128Mul_one_right, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-- Concrete stage transition: the first `7` stages (`6 ≤ rem`) apply a degree-1 linear weight
    combination `[m.t0, cl.targetErr]`, and the next `6` stages (`rem < 6`) apply a degree-3
    packed ternary sumcheck polynomial `[m.t0, cl.targetErr, m.t2, m.t3]`. -/
def rustBitStageStep (rem : Nat) (cl : RustBitStageClaim) (m : RustBitStageMsg)
    (coin : RustGf128) : RustBitStageClaim :=
  if 6 ≤ rem then
    { targetErr := RoundPoly.evalCoeffs [m.t0, cl.targetErr] coin, c0 := m.t0 }
  else
    { targetErr := RoundPoly.evalCoeffs [m.t0, cl.targetErr, m.t2, m.t3] coin, c0 := m.t0 }

private theorem rustBitStageStep_linear_le_one (rem : Nat) (hRem : 6 ≤ rem)
    (S : List RustGf128) (hS : S.Nodup) (cl : RustBitStageClaim) (m : RustBitStageMsg)
    (hFalse : decide ((rustBitStageEmbed cl).err ≠ 0#128) = true) :
    (S.filter (fun c =>
      !decide ((rustBitStageEmbed (rustBitStageStep rem cl m c)).err ≠ 0#128))).length ≤ 1 := by
  have hNe : cl.targetErr ≠ 0#128 := by
    have h := of_decide_eq_true hFalse
    rw [rustBitStageEmbed_err] at h
    exact h
  have hCount := rustGf128_roots_le_of_coeffAt_nonzero 1 [m.t0, cl.targetErr] 1 S hS
    (Nat.le_refl 2) (by decide) hNe
  have hPred : (fun c =>
      !decide ((rustBitStageEmbed (rustBitStageStep rem cl m c)).err ≠ 0#128)) =
      (fun c => decide (RoundPoly.evalCoeffs [m.t0, cl.targetErr] c = CommRingOps.zero)) := by
    funext c
    rw [rustBitStageEmbed_err]
    unfold rustBitStageStep
    rw [cIte_pos hRem]
    dsimp only
    by_cases hz : RoundPoly.evalCoeffs [m.t0, cl.targetErr] c = 0#128
    · rw [decide_eq_false (fun hne => hne hz), Bool.not_false]
      exact (decide_eq_true hz).symm
    · rw [decide_eq_true hz, Bool.not_true]
      exact (decide_eq_false hz).symm
  rw [hPred]; exact hCount

private theorem rustBitStageStep_ternary_le_three (rem : Nat) (hRem : ¬ (6 ≤ rem))
    (S : List RustGf128) (hS : S.Nodup) (cl : RustBitStageClaim) (m : RustBitStageMsg)
    (hFalse : decide ((rustBitStageEmbed cl).err ≠ 0#128) = true) :
    (S.filter (fun c =>
      !decide ((rustBitStageEmbed (rustBitStageStep rem cl m c)).err ≠ 0#128))).length ≤ 3 := by
  have hNe : cl.targetErr ≠ 0#128 := by
    have h := of_decide_eq_true hFalse
    rw [rustBitStageEmbed_err] at h
    exact h
  have hCount := rustGf128_roots_le_of_coeffAt_nonzero 3 [m.t0, cl.targetErr, m.t2, m.t3] 1 S hS
    (Nat.le_refl 4) (by decide) hNe
  have hPred : (fun c =>
      !decide ((rustBitStageEmbed (rustBitStageStep rem cl m c)).err ≠ 0#128)) =
      (fun c => decide (RoundPoly.evalCoeffs [m.t0, cl.targetErr, m.t2, m.t3] c = CommRingOps.zero)) := by
    funext c
    rw [rustBitStageEmbed_err]
    unfold rustBitStageStep
    simp only [hRem, ↓reduceIte]
    by_cases hz : RoundPoly.evalCoeffs [m.t0, cl.targetErr, m.t2, m.t3] c = 0#128
    · rw [decide_eq_false (fun hne => hne hz), Bool.not_false]
      exact (decide_eq_true hz).symm
    · rw [decide_eq_true hz, Bool.not_true]
      exact (decide_eq_false hz).symm
  rw [hPred]; exact hCount

/-- Constructive discharge of `StagesSound` for `rustBitCheckStageNumerators` (`7` linear weight
    stages + `6` degree-3 ternary sumcheck rounds). -/
theorem rustBitCheckStages_sound (S : List RustGf128) (hS : S.Nodup) :
    StagesSound S rustBitStageStep
      (fun cl => decide ((rustBitStageEmbed cl).err ≠ 0#128)) rustBitCheckStageNumerators := by
  show StagesSound S rustBitStageStep _ [1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3, 3, 3]
  refine ⟨rustBitStageStep_linear_le_one 12 (by decide) S hS,
    rustBitStageStep_linear_le_one 11 (by decide) S hS,
    rustBitStageStep_linear_le_one 10 (by decide) S hS,
    rustBitStageStep_linear_le_one 9 (by decide) S hS,
    rustBitStageStep_linear_le_one 8 (by decide) S hS,
    rustBitStageStep_linear_le_one 7 (by decide) S hS,
    rustBitStageStep_linear_le_one 6 (by decide) S hS,
    rustBitStageStep_ternary_le_three 5 (by decide) S hS,
    rustBitStageStep_ternary_le_three 4 (by decide) S hS,
    rustBitStageStep_ternary_le_three 3 (by decide) S hS,
    rustBitStageStep_ternary_le_three 2 (by decide) S hS,
    rustBitStageStep_ternary_le_three 1 (by decide) S hS,
    rustBitStageStep_ternary_le_three 0 (by decide) S hS,
    trivial⟩

/-- **Unconditional `BIT_CHECK_NUMERATOR = 63` Staged Acceptance Bound
    (`rust_bit_check_63_concrete_accepting_coins_bound`)**:
    With `StagesSound` discharged by `rustBitCheckStages_sound`, any adaptive prover starting
    from `(rustBitStageEmbed cl).err ≠ 0#128` across `rustBitCheckStageNumerators` + `18` halving
    rounds + nonzero base coin is accepted on at most `63 / (2^128 - 1)` of the coin space! -/
theorem rust_bit_check_63_concrete_accepting_coins_bound
    (p : StagedProver RustBitStageMsg (FoldProver rustBitCheckHalvingRounds) rustBitCheckStageNumerators)
    (cl : RustBitStageClaim) (hErr : (rustBitStageEmbed cl).err ≠ 0#128) :
    ((stagedCoinVectors productionFoldCoins
        (coinVectors productionFoldCoins productionBaseCoins rustBitCheckHalvingRounds)
        rustBitCheckStageNumerators).filter
      (stagedAccepts rustBitStageStep
        (fun q c coins => sacrificeAccepts rustBitCheckHalvingRounds q (rustBitStageEmbed c) coins)
        rustBitCheckStageNumerators p cl)).length * (2 ^ 128 - 1) ≤
      BIT_CHECK_NUMERATOR *
        (stagedCoinVectors productionFoldCoins
          (coinVectors productionFoldCoins productionBaseCoins rustBitCheckHalvingRounds)
          rustBitCheckStageNumerators).length := by
  have hStage := staged_sacrifice_false_claim_accepting_coins_bound
    productionFoldCoins productionBaseCoins productionFoldCoins_nodup productionBaseCoins_nodup
    rustBitCheckHalvingRounds rustBitStageStep rustBitStageEmbed rustBitCheckStageNumerators
    (rustBitCheckStages_sound productionFoldCoins productionFoldCoins_nodup) p cl hErr
  have hLen : (stagedCoinVectors productionFoldCoins
      (coinVectors productionFoldCoins productionBaseCoins rustBitCheckHalvingRounds)
      rustBitCheckStageNumerators).length =
      (2 ^ 128) ^ rustBitCheckStageNumerators.length *
        ((2 ^ 128) ^ rustBitCheckHalvingRounds * (2 ^ 128 - 1)) := by
    rw [stagedCoinVectors_length, coinVectors_length, productionFoldCoins_card, productionBaseCoins_card]
  rw [hLen]
  exact Nat.le_trans (Nat.mul_le_mul_right (2 ^ 128 - 1) (by
    rw [productionFoldCoins_card, productionBaseCoins_card] at hStage
    exact hStage)) rust_bit_check_numerator_63_bound.2.2.1

/-! #### Production `D0_BITS = 19` (`DEG_R0_PROD = 36`, `HALF_R0_PROD = 18`, `6 × 19 = 114` Super-Block)
    Round-0 Polynomial Reduction & 438-Repetition Ceremony Bound (`1 + 36 + 2 * 12 + 2 = 63`) -/

def packBlock114 (f : Nat → Bool) : RustGf128 :=
  rustSum 114 (fun k => if f k then BitVec.twoPow 128 k else 0#128)

theorem packBlock114_getLsbD (f : Nat → Bool) (i : Nat) (hi : i < 114) :
    (packBlock114 f).getLsbD i = f i := by
  unfold packBlock114
  rw [packBlock128_aux_bit 114 (by decide) f i, decide_eq_true hi, Bool.true_and]

def superBlock114And (pending : List PendingAnd) (q : Nat) (lane : Fin 64) : RustGf128 :=
  packBlock114 (fun k => gateLhsBit pending (114 * q + k) lane && gateRhsBit pending (114 * q + k) lane)

def superBlock114Z (pending : List PendingAnd) (q : Nat) (lane : Fin 64) : RustGf128 :=
  packBlock114 (fun k => gateOutBit pending (114 * q + k) lane)

def superBlock114Defect (pending : List PendingAnd) (q : Nat) (lane : Fin 64) : RustGf128 :=
  superBlock114And pending q lane ^^^ superBlock114Z pending q lane

theorem superBlock114Defect_ne_zero_of_gateErr (pending : List PendingAnd)
    (numSuper idx : Nat) (lane : Fin 64)
    (hIdx : idx < 114 * numSuper) (hErr : gateErrBit pending idx lane = true) :
    idx / 114 < numSuper ∧ superBlock114Defect pending (idx / 114) lane ≠ 0#128 := by
  refine ⟨by omega, ?_⟩
  intro hZero
  have hBit := congrArg (fun v : RustGf128 => v.getLsbD (idx % 114)) hZero
  have hRem : idx % 114 < 114 := Nat.mod_lt idx (by decide)
  have hDivMod : 114 * (idx / 114) + idx % 114 = idx := Nat.div_add_mod idx 114
  unfold superBlock114Defect superBlock114And superBlock114Z at hBit
  rw [BitVec.getLsbD_xor, packBlock114_getLsbD _ _ hRem, packBlock114_getLsbD _ _ hRem,
      hDivMod, BitVec.getLsbD_zero] at hBit
  unfold gateErrBit at hErr
  cases hout : gateOutBit pending idx lane <;>
    cases hand : (gateLhsBit pending idx lane && gateRhsBit pending idx lane) <;>
    simp only [hout, hand] at hErr hBit <;>
    cases hErr <;> cases hBit

def step0ZAcc114 (pending : List PendingAnd) (numSuper : Nat)
    (gammas : Nat → RustGf128) (lane : Fin 64) : RustGf128 :=
  rustDot numSuper gammas (fun q => superBlock114Z pending q lane)

def gamma114CombinedDefect (pending : List PendingAnd) (numSuper : Nat)
    (gammas : Nat → RustGf128) (lane : Fin 64) : RustGf128 :=
  rustDot numSuper gammas (fun q => superBlock114Defect pending q lane)

theorem gamma114CombinedDefect_bad_coins_le_one
    (pending : List PendingAnd) (numSuper qStar : Nat) (lane : Fin 64)
    (hq : qStar < numSuper)
    (hDefNe : superBlock114Defect pending qStar lane ≠ 0#128)
    (otherGammas : Nat → RustGf128)
    (S : List RustGf128) (hS : S.Nodup) :
    (S.filter (fun g =>
      decide (gamma114CombinedDefect pending numSuper (setGammaAt otherGammas qStar g) lane = 0#128))).length ≤ 1 := by
  let c0 := rustDot numSuper (setGammaAt otherGammas qStar 0#128)
    (fun q => superBlock114Defect pending q lane)
  let c1 := superBlock114Defect pending qStar lane
  have hCount := rustGf128_roots_le_of_coeffAt_nonzero 1 [c0, c1] 1 S hS (Nat.le_refl 2) (by decide) hDefNe
  have hPred : (fun g =>
      decide (gamma114CombinedDefect pending numSuper (setGammaAt otherGammas qStar g) lane = 0#128)) =
      (fun g => decide (RoundPoly.evalCoeffs [c0, c1] g = CommRingOps.zero)) := by
    funext g
    have hEq : gamma114CombinedDefect pending numSuper (setGammaAt otherGammas qStar g) lane =
        RoundPoly.evalCoeffs [c0, c1] g := by
      unfold gamma114CombinedDefect
      rw [rustDot_setGammaAt numSuper otherGammas _ qStar g hq]
      show c0 ^^^ rustGf128Mul g c1 = c0 ^^^ rustGf128Mul g (c1 ^^^ rustGf128Mul g 0#128)
      rw [rustGf128Mul_zero_right, BitVec.xor_zero]
    rw [hEq]; rfl
  rw [hPred]; exact hCount

/-- Block `A` and `B` polynomials of degree `< 19` (`D0_BITS_PROD = 19`, `HALF_R0_PROD = 18`). -/
def blockPolyA19 (pending : List PendingAnd) (base : Nat) (lane : Fin 64) : List RustGf128 :=
  List.ofFn (fun u : Fin 19 =>
    if gateLhsBit pending (base + u.val) lane then BitVec.twoPow 128 u.val else 0#128)

def blockPolyB19 (pending : List PendingAnd) (base : Nat) (w : RustGf128) (lane : Fin 64) :
    List RustGf128 :=
  List.ofFn (fun k : Fin 19 =>
    if gateRhsBit pending (base + (18 - k.val)) lane then w else 0#128)

/-- Round-0 claimed degree-`≤ 36` polynomial `H_0(r_0)` for `D0_BITS = 19`: slots `s ≠ 18` hold
    the prover's 36 cross-terms `h0`, while slot `s = 18` (`HALF_R0_PROD`) is locked to `zMid`! -/
def round0H0Coeffs19 (zMid : RustGf128) (h0 : Fin 36 → RustGf128) : List RustGf128 :=
  List.ofFn (fun s : Fin 37 =>
    if hs : s.val < 18 then h0 ⟨s.val, by omega⟩
    else if _ : s.val = 18 then zMid
    else h0 ⟨s.val - 1, by omega⟩)

def round0IpClaim19 (pending : List PendingAnd) (numSuper : Nat)
    (gammas : Nat → RustGf128) (h0 : Fin 36 → RustGf128)
    (r0 : RustGf128) (lane : Fin 64) : IpClaim where
  len := 6 * numSuper
  a := fun blk =>
    if blk < 6 * numSuper then
      RoundPoly.evalCoeffs (blockPolyA19 pending (114 * (blk / 6) + 19 * (blk % 6)) lane) r0
    else 0#128
  b := fun blk =>
    if blk < 6 * numSuper then
      RoundPoly.evalCoeffs
        (blockPolyB19 pending (114 * (blk / 6) + 19 * (blk % 6))
          (rustGf128Mul (gammas (blk / 6)) (BitVec.twoPow 128 (19 * (blk % 6)))) lane) r0
    else 0#128
  c := RoundPoly.evalCoeffs (round0H0Coeffs19 (step0ZAcc114 pending numSuper gammas lane) h0) r0

def round0DefectCoeffs19 (pending : List PendingAnd) (numSuper : Nat)
    (gammas : Nat → RustGf128) (h0 : Fin 36 → RustGf128) (lane : Fin 64) : List RustGf128 :=
  polyAddRust
    (polySumRust (6 * numSuper) (fun blk =>
      polyMulRust
        (blockPolyA19 pending (114 * (blk / 6) + 19 * (blk % 6)) lane)
        (blockPolyB19 pending (114 * (blk / 6) + 19 * (blk % 6))
          (rustGf128Mul (gammas (blk / 6)) (BitVec.twoPow 128 (19 * (blk % 6)))) lane)))
    (round0H0Coeffs19 (step0ZAcc114 pending numSuper gammas lane) h0)

/-- **Exact `D0_BITS = 19` Round-0 Polynomial Identity (`round0IpClaim19_err_eq_evalCoeffs`)**:
    1. `(round0IpClaim19 … r0 lane).err = RoundPoly.evalCoeffs (round0DefectCoeffs19 …) r0`,
    2. `(round0DefectCoeffs19 …).length ≤ 37` (`degree ≤ 36 = 2 * 19 - 2`),
    3. `coeffAt (round0DefectCoeffs19 …) 18 = gamma114CombinedDefect pending numSuper gammas lane`! -/
theorem round0IpClaim19_err_eq_evalCoeffs
    (pending : List PendingAnd) (numSuper : Nat)
    (gammas : Nat → RustGf128) (h0 : Fin 36 → RustGf128) (lane : Fin 64) :
    (∀ r0 : RustGf128,
      (round0IpClaim19 pending numSuper gammas h0 r0 lane).err =
        RoundPoly.evalCoeffs (round0DefectCoeffs19 pending numSuper gammas h0 lane) r0) ∧
    (round0DefectCoeffs19 pending numSuper gammas h0 lane).length ≤ 37 ∧
    coeffAt (round0DefectCoeffs19 pending numSuper gammas h0 lane) 18 =
      gamma114CombinedDefect pending numSuper gammas lane := by
  refine ⟨?_, ?_, ?_⟩
  · intro r0
    unfold IpClaim.err round0IpClaim19 round0DefectCoeffs19
    rw [evalCoeffs_polyAddRust, evalCoeffs_polySumRust]
    congr 1
    have hDotEqSum : ∀ m : Nat, m ≤ 6 * numSuper →
        rustDot m
          (fun blk => if blk < 6 * numSuper then
            RoundPoly.evalCoeffs (blockPolyA19 pending (114 * (blk / 6) + 19 * (blk % 6)) lane) r0 else 0#128)
          (fun blk => if blk < 6 * numSuper then
            RoundPoly.evalCoeffs (blockPolyB19 pending (114 * (blk / 6) + 19 * (blk % 6))
              (rustGf128Mul (gammas (blk / 6)) (BitVec.twoPow 128 (19 * (blk % 6)))) lane) r0 else 0#128) =
        rustSum m (fun blk =>
          RoundPoly.evalCoeffs
            (polyMulRust
              (blockPolyA19 pending (114 * (blk / 6) + 19 * (blk % 6)) lane)
              (blockPolyB19 pending (114 * (blk / 6) + 19 * (blk % 6))
                (rustGf128Mul (gammas (blk / 6)) (BitVec.twoPow 128 (19 * (blk % 6)))) lane)) r0) := by
      intro m hm
      induction m with
      | zero => rfl
      | succ m ih =>
        have hmLt : m < 6 * numSuper := by omega
        show rustDot m _ _ ^^^ rustGf128Mul (if m < 6 * numSuper then _ else 0#128)
            (if m < 6 * numSuper then _ else 0#128) =
          rustSum m _ ^^^ _
        rw [ih (by omega), cIte_pos hmLt, cIte_pos hmLt, ← evalCoeffs_polyMulRust]
    exact hDotEqSum (6 * numSuper) (Nat.le_refl _)
  · unfold round0DefectCoeffs19
    rw [polyAddRust_length]
    have hSumLe : (polySumRust (6 * numSuper) (fun blk =>
        polyMulRust
          (blockPolyA19 pending (114 * (blk / 6) + 19 * (blk % 6)) lane)
          (blockPolyB19 pending (114 * (blk / 6) + 19 * (blk % 6))
            (rustGf128Mul (gammas (blk / 6)) (BitVec.twoPow 128 (19 * (blk % 6)))) lane))).length ≤ 37 := by
      apply polySumRust_length_le 37
      intro blk _
      have hB : 1 ≤ (blockPolyB19 pending (114 * (blk / 6) + 19 * (blk % 6))
          (rustGf128Mul (gammas (blk / 6)) (BitVec.twoPow 128 (19 * (blk % 6)))) lane).length := by
        simp only [blockPolyB19, List.length_ofFn]
        decide
      have hMul := polyMulRust_length_le
        (blockPolyA19 pending (114 * (blk / 6) + 19 * (blk % 6)) lane) _ hB
      simp only [blockPolyA19, blockPolyB19, List.length_ofFn] at hMul
      exact hMul
    have hH0Len : (round0H0Coeffs19 (step0ZAcc114 pending numSuper gammas lane) h0).length = 37 := by
      simp only [round0H0Coeffs19, List.length_ofFn]
    exact Nat.max_le.mpr ⟨hSumLe, Nat.le_of_eq hH0Len⟩
  · unfold round0DefectCoeffs19
    rw [polyAddRust_coeffAt, polySumRust_coeffAt]
    have hH0Mid : coeffAt (round0H0Coeffs19 (step0ZAcc114 pending numSuper gammas lane) h0) 18 =
        step0ZAcc114 pending numSuper gammas lane := by
      unfold round0H0Coeffs19
      rw [coeffAt_ofFn, cDIte_pos (by decide : 18 < 37)]
      simp only [Nat.lt_irrefl, ↓reduceDIte]
    rw [hH0Mid]
    have hBlkMid : ∀ blk : Nat,
        coeffAt (polyMulRust
          (blockPolyA19 pending (114 * (blk / 6) + 19 * (blk % 6)) lane)
          (blockPolyB19 pending (114 * (blk / 6) + 19 * (blk % 6))
            (rustGf128Mul (gammas (blk / 6)) (BitVec.twoPow 128 (19 * (blk % 6)))) lane)) 18 =
        rustGf128Mul (gammas (blk / 6))
          (rustSum 19 (fun u =>
            if gateLhsBit pending (114 * (blk / 6) + 19 * (blk % 6) + u) lane &&
               gateRhsBit pending (114 * (blk / 6) + 19 * (blk % 6) + u) lane then
              BitVec.twoPow 128 (19 * (blk % 6) + u)
            else 0#128)) := by
      intro blk
      rw [polyMulRust_coeffAt, rustSum_mul_left]
      apply rustSum_congr
      intro u hu
      have hSub : 18 - u < 19 := by omega
      have hSubSub : 18 - (18 - u) = u := by omega
      have hSubLt6 : blk % 6 < 6 := Nat.mod_lt blk (by decide)
      unfold blockPolyA19 blockPolyB19
      rw [coeffAt_ofFn, coeffAt_ofFn, cDIte_pos hu, cDIte_pos hSub]
      dsimp only
      rw [hSubSub]
      cases gateLhsBit pending (114 * (blk / 6) + 19 * (blk % 6) + u) lane <;>
        cases gateRhsBit pending (114 * (blk / 6) + 19 * (blk % 6) + u) lane
      · simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
        rw [rustGf128Mul_zero_left, rustGf128Mul_zero_right]
      · simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
        rw [rustGf128Mul_zero_left, rustGf128Mul_zero_right]
      · simp only [Bool.and_false, Bool.false_eq_true, ↓reduceIte]
        rw [rustGf128Mul_zero_right, rustGf128Mul_zero_right]
      · simp only [Bool.and_self, ↓reduceIte]
        rw [rustGf128Mul_left_comm (BitVec.twoPow 128 u), rustGf128Mul_comm (BitVec.twoPow 128 u),
            rustTwoPow_mul (19 * (blk % 6)) u (by omega)]
    have hSumEq : rustSum (6 * numSuper) (fun blk =>
        coeffAt (polyMulRust
          (blockPolyA19 pending (114 * (blk / 6) + 19 * (blk % 6)) lane)
          (blockPolyB19 pending (114 * (blk / 6) + 19 * (blk % 6))
            (rustGf128Mul (gammas (blk / 6)) (BitVec.twoPow 128 (19 * (blk % 6)))) lane)) 18) =
        rustDot numSuper gammas (fun q => superBlock114And pending q lane) := by
      have hRewrite : rustSum (6 * numSuper) (fun blk =>
          coeffAt (polyMulRust
            (blockPolyA19 pending (114 * (blk / 6) + 19 * (blk % 6)) lane)
            (blockPolyB19 pending (114 * (blk / 6) + 19 * (blk % 6))
              (rustGf128Mul (gammas (blk / 6)) (BitVec.twoPow 128 (19 * (blk % 6)))) lane)) 18) =
          rustSum (numSuper * 6) (fun blk =>
            rustGf128Mul (gammas (blk / 6))
              (rustSum 19 (fun u =>
                if gateLhsBit pending (114 * (blk / 6) + 19 * (blk % 6) + u) lane &&
                   gateRhsBit pending (114 * (blk / 6) + 19 * (blk % 6) + u) lane then
                  BitVec.twoPow 128 (19 * (blk % 6) + u)
                else 0#128))) := by
        rw [Nat.mul_comm 6 numSuper]
        exact rustSum_congr (numSuper * 6) (fun blk _ => hBlkMid blk)
      rw [hRewrite, rustSum_blocks numSuper 6]
      have hDotAsSum : ∀ m : Nat,
          rustDot m gammas (fun q => superBlock114And pending q lane) =
            rustSum m (fun q => rustGf128Mul (gammas q) (superBlock114And pending q lane)) := by
        intro m
        induction m with
        | zero => rfl
        | succ m ih => show rustDot m _ _ ^^^ _ = rustSum m _ ^^^ _; rw [ih]
      rw [hDotAsSum]
      apply rustSum_congr
      intro q _
      have hSuperSplit : superBlock114And pending q lane =
          rustSum 6 (fun sub => rustSum 19 (fun u =>
            if gateLhsBit pending (114 * q + (19 * sub + u)) lane &&
               gateRhsBit pending (114 * q + (19 * sub + u)) lane then
              BitVec.twoPow 128 (19 * sub + u)
            else 0#128)) :=
        rustSum_blocks 6 19 (fun k =>
          if gateLhsBit pending (114 * q + k) lane && gateRhsBit pending (114 * q + k) lane then
            BitVec.twoPow 128 k
          else 0#128)
      rw [hSuperSplit, rustSum_mul_left]
      apply rustSum_congr
      intro sub hSub
      have hDiv : (6 * q + sub) / 6 = q := by omega
      have hMod : (6 * q + sub) % 6 = sub := by omega
      rw [hDiv, hMod]
      apply congrArg (rustGf128Mul (gammas q))
      apply rustSum_congr
      intro u _
      rw [Nat.add_assoc (114 * q) (19 * sub) u]
    rw [hSumEq]
    unfold step0ZAcc114 gamma114CombinedDefect superBlock114Defect
    have hXorDot : ∀ m : Nat,
        rustDot m gammas (fun q => superBlock114And pending q lane) ^^^
          rustDot m gammas (fun q => superBlock114Z pending q lane) =
        rustDot m gammas (fun q => superBlock114And pending q lane ^^^ superBlock114Z pending q lane) := by
      intro m
      induction m with
      | zero => simp only [rustDot]; decide
      | succ m ih =>
        let A := rustDot m gammas (fun q => superBlock114And pending q lane)
        let B := rustDot m gammas (fun q => superBlock114Z pending q lane)
        let X := rustGf128Mul (gammas m) (superBlock114And pending m lane)
        let Y := rustGf128Mul (gammas m) (superBlock114Z pending m lane)
        show (A ^^^ X) ^^^ (B ^^^ Y) =
          rustDot m gammas (fun q => superBlock114And pending q lane ^^^ superBlock114Z pending q lane) ^^^
            rustGf128Mul (gammas m) (superBlock114And pending m lane ^^^ superBlock114Z pending m lane)
        rw [rustGf128Mul_xor_right, ← ih]
        show (A ^^^ X) ^^^ (B ^^^ Y) = (A ^^^ B) ^^^ (X ^^^ Y)
        rw [BitVec.xor_assoc A X (B ^^^ Y), ← BitVec.xor_assoc X B Y,
            BitVec.xor_comm X B, BitVec.xor_assoc B X Y, ← BitVec.xor_assoc A B (X ^^^ Y)]
    exact hXorDot numSuper

/-- **`D0_BITS = 19` Round-0 Soundness (`round0_d19_false_gamma_survives_at_most_36_coins`)**:
    Whenever `gamma114CombinedDefect pending numSuper gammas lane ≠ 0#128`, for ANY maliciously
    chosen cross-terms `h0 : Fin 36 → RustGf128`, at most `36` (`2 * D0_BITS_PROD - 2`) challenges
    `r0 ∈ S` make `(round0IpClaim19 … r0 lane).err = 0#128`! -/
theorem round0_d19_false_gamma_survives_at_most_36_coins
    (pending : List PendingAnd) (numSuper : Nat)
    (gammas : Nat → RustGf128) (h0 : Fin 36 → RustGf128) (lane : Fin 64)
    (hGammaNe : gamma114CombinedDefect pending numSuper gammas lane ≠ 0#128)
    (S : List RustGf128) (hS : S.Nodup) :
    (S.filter (fun r0 =>
      decide ((round0IpClaim19 pending numSuper gammas h0 r0 lane).err = 0#128))).length ≤ 36 := by
  have ⟨hEval, hLen, hMid⟩ := round0IpClaim19_err_eq_evalCoeffs pending numSuper gammas h0 lane
  have hMidNe : coeffAt (round0DefectCoeffs19 pending numSuper gammas h0 lane) 18 ≠ 0#128 := by
    rw [hMid]; exact hGammaNe
  have hCount := rustGf128_roots_le_of_coeffAt_nonzero 36
    (round0DefectCoeffs19 pending numSuper gammas h0 lane) 18 S hS hLen (by decide) hMidNe
  have hPred : (fun r0 =>
      decide ((round0IpClaim19 pending numSuper gammas h0 r0 lane).err = 0#128)) =
      (fun r0 => decide (RoundPoly.evalCoeffs
        (round0DefectCoeffs19 pending numSuper gammas h0 lane) r0 = CommRingOps.zero)) := by
    funext r0; rw [hEval r0]; rfl
  rw [hPred]; exact hCount

def round0D19FlushClaims (pending : List PendingAnd) (numSuper : Nat)
    (gammas : Nat → RustGf128) (h0 : Fin 2 → Fin 64 → Fin 36 → RustGf128)
    (r0 : CoinPair) : FlushClaims :=
  fun t lane => round0IpClaim19 pending numSuper gammas (h0 t lane) (coinAt r0 t) lane

structure Round0D19FlushProver (r : Nat) where
  h0 : Fin 2 → Fin 64 → Fin 36 → RustGf128
  afterR0 : CoinPair → FlushProver r

def round0D19FlushAccepts (r : Nat) (pending : List PendingAnd) (numSuper : Nat)
    (gammas : Nat → RustGf128) (p : Round0D19FlushProver r) : List CoinPair → Bool
  | [] => false
  | r0 :: rest =>
    flushAccepts r (p.afterR0 r0) (round0D19FlushClaims pending numSuper gammas p.h0 r0) rest

/-- Single-instance bad-coin count across `D0_BITS = 19` Round 0 (`36`) + `r` binary folds (`2r`) + base (`2`).
    Combined with `1` `γ`-combiner coin at `r = 12`, the total numerator is `1 + 36 + 24 + 2 = 63 = BIT_CHECK_NUMERATOR`! -/
def round0D19SacrificeBadBound (n nb r : Nat) : Nat :=
  36 * (n ^ r * nb) + n * sacrificeBadCoinBound n nb r

theorem round0D19Flush_false_gamma_accepting_coins_bound
    (S Sb : List RustGf128) (hS : S.Nodup) (hSb : Sb.Nodup) (r : Nat)
    (pending : List PendingAnd) (numSuper : Nat) (gammas : Nat → RustGf128)
    (p : Round0D19FlushProver r) (lane : Fin 64)
    (hGammaNe : gamma114CombinedDefect pending numSuper gammas lane ≠ 0#128) :
    ((flushCoinVectors S Sb (r + 1)).filter
      (round0D19FlushAccepts r pending numSuper gammas p)).length ≤
      round0D19SacrificeBadBound S.length Sb.length r *
        round0D19SacrificeBadBound S.length Sb.length r := by
  have hCount : ((flushCoinVectors S Sb (r + 1)).filter
      (round0D19FlushAccepts r pending numSuper gammas p)).length =
      (S.map (fun a => (S.map (fun b =>
        flushAccepting S Sb r (p.afterR0 (a, b))
          (round0D19FlushClaims pending numSuper gammas p.h0 (a, b)))).sum)).sum := by
    show (((coinPairs S).flatMap (fun r0 => (flushCoinVectors S Sb r).map (fun rest => r0 :: rest))).filter
      (round0D19FlushAccepts r pending numSuper gammas p)).length = _
    rw [filter_flatMap_length]
    have hMapEq : ((coinPairs S).map (fun r0 =>
        (((flushCoinVectors S Sb r).map (fun rest => r0 :: rest)).filter
          (round0D19FlushAccepts r pending numSuper gammas p)).length)) =
        ((coinPairs S).map (fun r0 =>
          flushAccepting S Sb r (p.afterR0 r0)
            (round0D19FlushClaims pending numSuper gammas p.h0 r0))) := by
      apply List.map_congr_left
      intro r0 _
      rw [filter_map_length, flushAccepting_eq_filter]
      rfl
    rw [hMapEq]
    exact sum_map_pairs (fun r0 =>
      flushAccepting S Sb r (p.afterR0 r0)
        (round0D19FlushClaims pending numSuper gammas p.h0 r0)) S S
  let w0 : RustGf128 → Nat := fun a =>
    laneWeight S.length Sb.length
      (decide ((round0IpClaim19 pending numSuper gammas (p.h0 0 lane) a lane).err ≠ 0#128)) r
  let w1 : RustGf128 → Nat := fun b =>
    laneWeight S.length Sb.length
      (decide ((round0IpClaim19 pending numSuper gammas (p.h0 1 lane) b lane).err ≠ 0#128)) r
  have hCell : ∀ a b, flushAccepting S Sb r (p.afterR0 (a, b))
      (round0D19FlushClaims pending numSuper gammas p.h0 (a, b)) ≤ w0 a * w1 b := by
    intro a b
    exact flushAccepting_le_weights S Sb hS hSb lane r (p.afterR0 (a, b))
      (round0D19FlushClaims pending numSuper gammas p.h0 (a, b))
      (decide ((round0IpClaim19 pending numSuper gammas (p.h0 0 lane) a lane).err ≠ 0#128))
      (decide ((round0IpClaim19 pending numSuper gammas (p.h0 1 lane) b lane).err ≠ 0#128))
      (fun h => of_decide_eq_true h) (fun h => of_decide_eq_true h)
  have hW0 : (S.map w0).sum ≤ round0D19SacrificeBadBound S.length Sb.length r := by
    have hSplit := sum_map_le_cases
      (fun a => decide ((round0IpClaim19 pending numSuper gammas (p.h0 0 lane) a lane).err = 0#128))
      w0 (S.length ^ r * Sb.length) (sacrificeBadCoinBound S.length Sb.length r)
      (fun a hb => by
        dsimp only [w0]
        rw [decide_eq_false (fun hne => hne (of_decide_eq_true hb))]
        exact Nat.le_refl _)
      (fun a hg => by
        dsimp only [w0]
        rw [decide_eq_true (of_decide_eq_false hg)]
        exact Nat.le_refl _) S
    have hBad := round0_d19_false_gamma_survives_at_most_36_coins pending numSuper gammas
      (p.h0 0 lane) lane hGammaNe S hS
    have hMul := Nat.mul_le_mul_right (S.length ^ r * Sb.length) hBad
    unfold round0D19SacrificeBadBound
    omega
  have hW1 : (S.map w1).sum ≤ round0D19SacrificeBadBound S.length Sb.length r := by
    have hSplit := sum_map_le_cases
      (fun b => decide ((round0IpClaim19 pending numSuper gammas (p.h0 1 lane) b lane).err = 0#128))
      w1 (S.length ^ r * Sb.length) (sacrificeBadCoinBound S.length Sb.length r)
      (fun b hb => by
        dsimp only [w1]
        rw [decide_eq_false (fun hne => hne (of_decide_eq_true hb))]
        exact Nat.le_refl _)
      (fun b hg => by
        dsimp only [w1]
        rw [decide_eq_true (of_decide_eq_false hg)]
        exact Nat.le_refl _) S
    have hBad := round0_d19_false_gamma_survives_at_most_36_coins pending numSuper gammas
      (p.h0 1 lane) lane hGammaNe S hS
    have hMul := Nat.mul_le_mul_right (S.length ^ r * Sb.length) hBad
    unfold round0D19SacrificeBadBound
    omega
  rw [hCount]
  calc (S.map (fun a => (S.map (fun b =>
          flushAccepting S Sb r (p.afterR0 (a, b))
            (round0D19FlushClaims pending numSuper gammas p.h0 (a, b)))).sum)).sum
      ≤ (S.map (fun a => (S.map (fun b => w0 a * w1 b)).sum)).sum :=
        sum_map_le_sum_map _ _ (fun a => sum_map_le_sum_map _ _ (fun b => hCell a b) S) S
    _ = (S.map w0).sum * (S.map w1).sum := sum_sum_mul w0 w1 S S
    _ ≤ round0D19SacrificeBadBound S.length Sb.length r *
          round0D19SacrificeBadBound S.length Sb.length r := Nat.mul_le_mul hW0 hW1

/-- **`D0_BITS = 19` (`BIT_CHECK_NUMERATOR = 63`) Bound (`d19_round0_sacrifice_bit_check_63_bound`)**:
    1. Across `γ` (`1`) + `D0_BITS = 19` Round 0 (`36`) + `12` binary folds (`24`) + base (`2`),
       the single-instance numerator is `63 = BIT_CHECK_NUMERATOR` (`≤ 63 / (2^128 - 1)`),
    2. Across two lockstep instances, `(round0D19SacrificeBadBound)² < 2^-244` for all `r ≤ 12`! -/
theorem d19_round0_sacrifice_bit_check_63_bound :
    (1 * ((2 ^ 128) ^ 13 * (2 ^ 128 - 1)) +
      2 ^ 128 * round0D19SacrificeBadBound (2 ^ 128) (2 ^ 128 - 1) 12) * (2 ^ 128 - 1) ≤
      BIT_CHECK_NUMERATOR * ((2 ^ 128) ^ 14 * (2 ^ 128 - 1)) ∧
    ∀ r, r ≤ 12 →
      round0D19SacrificeBadBound (2 ^ 128) (2 ^ 128 - 1) r *
        round0D19SacrificeBadBound (2 ^ 128) (2 ^ 128 - 1) r * 2 ^ 244 ≤
      ((2 ^ 128) ^ (r + 1) * (2 ^ 128 - 1)) * ((2 ^ 128) ^ (r + 1) * (2 ^ 128 - 1)) := by
  decide +kernel

abbrev FullD19CeremonyProver (r : Nat) := Fin 7 → FullCeremonyCoins → Round0D19FlushProver r

def FullD19ForkStrategiesPrecedeOwnCoins {r : Nat} (p : FullD19CeremonyProver r) : Prop :=
  ∀ (b : Fin 7) (c : FullCeremonyCoins) (gv : RustGf128 × List CoinPair),
    p b (setFullForkCoins c b gv) = p b c

def fullD19CeremonyAccepts (r : Nat) (st : Fin 7 → GateState) (numSuper : Fin 7 → Nat)
    (otherGammas : Fin 7 → Nat → RustGf128) (qFocus : Fin 7 → Nat)
    (p : FullD19CeremonyProver r) (coins : FullCeremonyCoins) : Bool :=
  finAll 7 (fun b =>
    round0D19FlushAccepts r (st b).pending (numSuper b)
      (setGammaAt (otherGammas b) (qFocus b) (coins b).1) (p b coins) (coins b).2)

/-- **Unconditional `D0_BITS = 19` (`BIT_CHECK_NUMERATOR = 63`) 438-Repetition Ceremony Soundness
    (`migration_d19_unconditional_circuit_to_sacrifice_ceremony_bound`)** -/
theorem migration_d19_unconditional_circuit_to_sacrifice_ceremony_bound
    (gates : List Gate) (relB : MigrationKey256 → Bool) (hCirc : CircuitSoundForRel gates relB)
    (batches : MigrationWitnessBatches) (hB : MigrationBatchConsistent batches)
    (hFalse : relB (extractRepetitionWitness (batches 0) 0) = false)
    (st : Fin 7 → GateState) (numSuper : Fin 7 → Nat)
    (hEval : ∀ b : Fin 7, evalGates ⟨witnessWires (batches b), []⟩ gates = some (st b))
    (hOpen : ∀ b : Fin 7, finishWithoutCheck (st b) = .accepted)
    (hCap : ∀ b : Fin 7, (st b).pending.length ≤ 114 * numSuper b)
    (r : Nat) (hr : r ≤ 12)
    (otherGammas : Fin 7 → Nat → RustGf128)
    (p : FullD19CeremonyProver r) (hOwn : FullD19ForkStrategiesPrecedeOwnCoins p) :
    ∀ (rep : Fin 438) (others : FullCeremonyCoins),
      let b := repetitionFork rep
      let lane := repetitionLane rep
      relB (migrationRepetitionWitness batches rep) = false ∧
      ∃ qStar : Nat, qStar < numSuper b ∧
        superBlock114Defect (st b).pending qStar lane ≠ 0#128 ∧
        ((fullFlushCoinSpace productionFoldCoins productionBaseCoins r).filter (fun gv =>
          fullD19CeremonyAccepts r st numSuper otherGammas
            (fun b' => if b' = b then qStar else 0) p
            (setFullForkCoins others b gv))).length * 2 ^ 127 ≤
          (fullFlushCoinSpace productionFoldCoins productionBaseCoins r).length := by
  intro rep others b lane
  have hRepEq := migration_all_438_repetitions_same_witness batches hB rep
  have hRepFalse : relB (migrationRepetitionWitness batches rep) = false := by
    rw [hRepEq]; exact hFalse
  refine ⟨hRepFalse, ?_⟩
  have hWireTrue := wireBit_true_of_finishWithoutCheck (st b) lane (hOpen b)
  obtain ⟨idx, hIdxLt, hIdxErr⟩ := false_witness_implies_pending_and_fault gates relB hCirc
    (batches b) lane hRepFalse (st b) (hEval b) hWireTrue
  have hGateErr : gateErrBit (st b).pending idx lane = true := by
    unfold gateErrBit gateOutBit gateLhsBit gateRhsBit
    cases hp : (st b).pending[idx]? with
    | none => rw [hp] at hIdxErr; cases hIdxErr
    | some t => rw [hp] at hIdxErr; exact Option.some.inj hIdxErr
  have ⟨hqLt, hSuperNe⟩ := superBlock114Defect_ne_zero_of_gateErr (st b).pending (numSuper b) idx lane
    (Nat.lt_of_lt_of_le hIdxLt (hCap b)) hGateErr
  let qStar := idx / 114
  refine ⟨qStar, hqLt, hSuperNe, ?_⟩
  let S := productionFoldCoins
  let Sb := productionBaseCoins
  let qFocus : Fin 7 → Nat := fun b' => if b' = b then qStar else 0
  have hFocusSelf : qFocus b = qStar := by simp only [qFocus, ↓reduceIte]
  let V := flushCoinVectors S Sb (r + 1)
  have hImp : ∀ g v,
      fullD19CeremonyAccepts r st numSuper otherGammas qFocus p (setFullForkCoins others b (g, v)) = true →
      round0D19FlushAccepts r (st b).pending (numSuper b)
        (setGammaAt (otherGammas b) qStar g) (p b others) v = true := by
    intro g v hv
    have hb := (finAll_eq_true_iff 7 _).mp hv b
    have hSelf : setFullForkCoins others b (g, v) b = (g, v) := by
      simp only [setFullForkCoins, ↓reduceIte]
    rw [hOwn b others (g, v), hSelf, hFocusSelf] at hb
    exact hb
  have hCountLe : ((fullFlushCoinSpace S Sb r).filter (fun gv =>
      fullD19CeremonyAccepts r st numSuper otherGammas qFocus p (setFullForkCoins others b gv))).length ≤
      (S.map (fun g => (V.filter (round0D19FlushAccepts r (st b).pending (numSuper b)
        (setGammaAt (otherGammas b) qStar g) (p b others))).length)).sum := by
    unfold fullFlushCoinSpace
    rw [filter_flatMap_length]
    apply sum_map_le_sum_map
    intro g
    rw [filter_map_length]
    exact filter_length_le_of_imp _ _ (fun v hv => hImp g v hv) V
  let T := V.length
  let B := round0D19SacrificeBadBound S.length Sb.length r *
             round0D19SacrificeBadBound S.length Sb.length r
  have hSplit := sum_map_le_cases
    (fun g => decide (gamma114CombinedDefect (st b).pending (numSuper b)
      (setGammaAt (otherGammas b) qStar g) lane = 0#128))
    (fun g => (V.filter (round0D19FlushAccepts r (st b).pending (numSuper b)
      (setGammaAt (otherGammas b) qStar g) (p b others))).length)
    T B
    (fun g _ => List.length_filter_le _ V)
    (fun g hg => round0D19Flush_false_gamma_accepting_coins_bound S Sb
      productionFoldCoins_nodup productionBaseCoins_nodup r
      (st b).pending (numSuper b) (setGammaAt (otherGammas b) qStar g)
      (p b others) lane (of_decide_eq_false hg))
    S
  have hBadGamma := gamma114CombinedDefect_bad_coins_le_one (st b).pending (numSuper b) qStar lane
    hqLt hSuperNe (otherGammas b) S productionFoldCoins_nodup
  have hSumLe : (S.map (fun g => (V.filter (round0D19FlushAccepts r (st b).pending (numSuper b)
      (setGammaAt (otherGammas b) qStar g) (p b others))).length)).sum ≤ 1 * T + S.length * B :=
    Nat.le_trans hSplit (Nat.add_le_add_right (Nat.mul_le_mul_right T hBadGamma) _)
  have hTotalLen : (fullFlushCoinSpace S Sb r).length = S.length * T :=
    flatMap_map_length V (fun g v => (g, v)) S
  have hArith : (1 * T + S.length * B) * 2 ^ 127 ≤ S.length * T := by
    dsimp only [T, B, V]
    rw [flushCoinVectors_length, productionFoldCoins_card, productionBaseCoins_card]
    have hR0 := d19_round0_sacrifice_bit_check_63_bound.2 r hr
    generalize ((2 ^ 128) ^ (r + 1) * (2 ^ 128 - 1)) * ((2 ^ 128) ^ (r + 1) * (2 ^ 128 - 1)) = M at hR0 ⊢
    generalize round0D19SacrificeBadBound (2 ^ 128) (2 ^ 128 - 1) r *
        round0D19SacrificeBadBound (2 ^ 128) (2 ^ 128 - 1) r = K at hR0 ⊢
    have h128le244 : 2 ^ 128 ≤ 2 ^ 244 :=
      Nat.pow_le_pow_right (by decide : 0 < 2) (by decide : 128 ≤ 244)
    have hB128 : K * 2 ^ 128 ≤ M := Nat.le_trans (Nat.mul_le_mul_left K h128le244) hR0
    rw [Nat.one_mul, Nat.add_mul]
    have hK2 : (2 ^ 128 * K) * 2 ^ 127 = (K * 2 ^ 128) * 2 ^ 127 := by
      rw [Nat.mul_comm (2 ^ 128) K]
    rw [hK2]
    have hHalf : M * 2 ^ 127 + (K * 2 ^ 128) * 2 ^ 127 ≤ M * 2 ^ 127 + M * 2 ^ 127 :=
      Nat.add_le_add_left (Nat.mul_le_mul_right (2 ^ 127) hB128) _
    have hDouble : M * 2 ^ 127 + M * 2 ^ 127 = 2 ^ 128 * M := by
      have h2 : (2 ^ 128 : Nat) = 2 ^ 127 + 2 ^ 127 := by
        rw [Nat.pow_succ 2 127, Nat.mul_two]
      rw [h2, Nat.add_mul, Nat.mul_comm M (2 ^ 127)]
    exact hDouble ▸ hHalf
  rw [hTotalLen]
  exact Nat.le_trans (Nat.mul_le_mul_right (2 ^ 127) (Nat.le_trans hCountLe hSumLe)) hArith

/-! ### 11C. Prime-Field Multiplication Check `FIELD_CHECK_NUMERATOR = 35`
    (`verify_pending_large_prime_slice`, `outer_mpc.rs:43, 1873-2055`) -/

section PrimeFieldCheck
open scoped Qsag.CRing

/-- One scalar prime-field multiplication lane `(x, y, z)` (`outer_mpc.rs:1927-1935`). -/
structure FpTriple (F : Type) where
  x : F
  y : F
  z : F

def FpTriple.defect {F : Type} [CommRingOps F] (t : FpTriple F) : F :=
  t.x * t.y - t.z

def fpSum {F : Type} [CommRingOps F] : Nat → (Nat → F) → F
  | 0, _ => 0
  | n + 1, f => fpSum n f + f n

def fpDot {F : Type} [CommRingOps F] : Nat → (Nat → F) → (Nat → F) → F
  | 0, _, _ => 0
  | n + 1, a, b => fpDot n a b + a n * b n

/-- Inner-product claim `∑_{i < len} a_i · b_i = c` over a prime field `F`. -/
structure FpIpClaim (F : Type) where
  len : Nat
  a : Nat → F
  b : Nat → F
  c : F

def FpIpClaim.err {F : Type} [CommRingOps F] (s : FpIpClaim F) : F :=
  fpDot s.len s.a s.b - s.c

def setFpChiAt {F : Type} (chis : Nat → F) (iStar : Nat) (chi : F) : Nat → F :=
  fun i => if i = iStar then chi else chis i

/-- Step 1 of `verify_pending_large_prime_slice` (`QSAG.OUTER.MULCHECK.FP.INIT.V1`):
    random linear combination scaling `a_i := χ_i · x_i`, `b_i := y_i`, `c := ∑ χ_i · z_i`. -/
def fpRlcClaim {F : Type} [CommRingOps F] (N : Nat) (triples : Nat → FpTriple F)
    (chis : Nat → F) : FpIpClaim F where
  len := N
  a := fun i => if i < N then chis i * (triples i).x else 0
  b := fun i => if i < N then (triples i).y else 0
  c := fpSum N (fun i => chis i * (triples i).z)

theorem fpRlcClaim_err_eq_dot {F : Type} [LawfulCommRing F]
    (N : Nat) (triples : Nat → FpTriple F) (chis : Nat → F) :
    (fpRlcClaim N triples chis).err = fpDot N chis (fun i => (triples i).defect) := by
  unfold FpIpClaim.err fpRlcClaim
  dsimp only
  have hGen : ∀ m : Nat, m ≤ N →
      fpDot m (fun i => if i < N then chis i * (triples i).x else 0)
              (fun i => if i < N then (triples i).y else 0) -
        fpSum m (fun i => chis i * (triples i).z) =
      fpDot m chis (fun i => (triples i).defect) := by
    intro m hm
    induction m with
    | zero =>
      show (0 : F) - 0 = 0
      constructive_ring
    | succ m ih =>
      have hmLt : m < N := by omega
      dsimp only [fpDot, fpSum, FpTriple.defect]
      rw [cIte_pos hmLt, cIte_pos hmLt]
      have hPrev := ih (by omega)
      show (fpDot m (fun i => if i < N then chis i * (triples i).x else 0)
                    (fun i => if i < N then (triples i).y else 0) +
             (chis m * (triples m).x) * (triples m).y) -
           (fpSum m (fun i => chis i * (triples i).z) + chis m * (triples m).z) =
           fpDot m chis (fun i => (triples i).defect) +
             chis m * ((triples m).x * (triples m).y - (triples m).z)
      rw [← hPrev]
      constructive_ring
  exact hGen N (Nat.le_refl N)

private theorem fpDot_congr {F : Type} [CommRingOps F] :
    ∀ (n : Nat) {a a' b b' : Nat → F},
      (∀ i, i < n → a i = a' i) → (∀ i, i < n → b i = b' i) →
      fpDot n a b = fpDot n a' b'
  | 0, _, _, _, _, _, _ => rfl
  | n + 1, a, a', b, b', ha, hb => by
    show fpDot n a b + a n * b n = fpDot n a' b' + a' n * b' n
    rw [fpDot_congr n (fun i hi => ha i (by omega)) (fun i hi => hb i (by omega)),
        ha n (by omega), hb n (by omega)]

theorem fpDot_setFpChiAt {F : Type} [LawfulCommRing F] :
    ∀ (n : Nat) (chis : Nat → F) (d : Nat → F) (iStar : Nat) (chi : F),
      iStar < n →
      fpDot n (setFpChiAt chis iStar chi) d =
        fpDot n (setFpChiAt chis iStar 0) d + chi * d iStar
  | 0, _, _, _, _, h => nomatch h
  | n + 1, chis, d, iStar, chi, hLt => by
    rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp hLt) with rfl | hLt'
    · show fpDot iStar (setFpChiAt chis iStar chi) d +
          setFpChiAt chis iStar chi iStar * d iStar =
        (fpDot iStar (setFpChiAt chis iStar 0) d +
          setFpChiAt chis iStar 0 iStar * d iStar) + chi * d iStar
      have hRest : fpDot iStar (setFpChiAt chis iStar chi) d =
          fpDot iStar (setFpChiAt chis iStar 0) d :=
        fpDot_congr iStar
          (fun i hi => by simp only [setFpChiAt, show ¬ i = iStar from by omega, ↓reduceIte])
          (fun _ _ => rfl)
      simp only [hRest, setFpChiAt, ↓reduceIte]
      constructive_ring
    · have ih := fpDot_setFpChiAt n chis d iStar chi hLt'
      show fpDot n (setFpChiAt chis iStar chi) d +
          setFpChiAt chis iStar chi n * d n =
        (fpDot n (setFpChiAt chis iStar 0) d +
          setFpChiAt chis iStar 0 n * d n) + chi * d iStar
      rw [ih]
      simp only [setFpChiAt, show ¬ n = iStar from by omega, ↓reduceIte]
      constructive_ring

/-- **Step-1 RLC Soundness (`fpRlc_false_triple_survives_at_most_one_coin`)**:
    If triple `iStar < N` has `(triples iStar).defect ≠ 0`, then for any fixed values of the other
    `χ` challenges, at most `1` value of `χ_{iStar} ∈ S` cancels `(fpRlcClaim …).err`! -/
theorem fpRlc_false_triple_survives_at_most_one_coin
    {F : Type} [LawfulCommRing F] [DecidableEq F] [NoZeroDivisors F]
    (N iStar : Nat) (triples : Nat → FpTriple F)
    (hi : iStar < N) (hDefNe : (triples iStar).defect ≠ 0)
    (otherChis : Nat → F) (S : List F) (hS : S.Nodup) :
    (S.filter (fun chi =>
      decide ((fpRlcClaim N triples (setFpChiAt otherChis iStar chi)).err = 0))).length ≤ 1 := by
  let c0 := fpDot N (setFpChiAt otherChis iStar 0) (fun i => (triples i).defect)
  let c1 := (triples iStar).defect
  have hEx : ∃ c ∈ ([c0, c1] : List F), c ≠ CommRingOps.zero :=
    ⟨c1, List.Mem.tail _ (List.Mem.head _), hDefNe⟩
  have hEvalEq : ∀ chi : F,
      (fpRlcClaim N triples (setFpChiAt otherChis iStar chi)).err =
        RoundPoly.evalCoeffs [c0, c1] chi := by
    intro chi
    rw [fpRlcClaim_err_eq_dot, fpDot_setFpChiAt N otherChis _ iStar chi hi]
    show c0 + chi * c1 = c0 + chi * (c1 + chi * 0)
    constructive_ring
  exact gs_formal_root_bound 1 [c0, c1]
    (S.filter (fun chi => decide ((fpRlcClaim N triples (setFpChiAt otherChis iStar chi)).err = 0)))
    (Nat.le_refl 2) hEx (hS.filter _)
    (fun chi hMem => by
      have hDec := (List.mem_filter.mp hMem).2
      rw [← hEvalEq chi]
      exact of_decide_eq_true hDec)

/-- Reshared cross-terms `(d0, d1)` sent by the prover in one `verify_pending_large_prime_slice` fold round. -/
structure FpFoldMsg (F : Type) where
  d0 : F
  d1 : F

def FpIpClaim.half {F : Type} (s : FpIpClaim F) : Nat := (s.len + 1) / 2

def FpIpClaim.padA {F : Type} [CommRingOps F] (s : FpIpClaim F) (i : Nat) : F :=
  if i < s.len then s.a i else 0

def FpIpClaim.padB {F : Type} [CommRingOps F] (s : FpIpClaim F) (i : Nat) : F :=
  if i < s.len then s.b i else 0

def FpIpClaim.crossLoHi {F : Type} [CommRingOps F] (s : FpIpClaim F) : F :=
  fpSum s.half (fun k => s.padA (2 * k) * s.padB (2 * k + 1))

def FpIpClaim.crossHiLo {F : Type} [CommRingOps F] (s : FpIpClaim F) : F :=
  fpSum s.half (fun k => s.padA (2 * k + 1) * s.padB (2 * k))

/-- Step 2 of `verify_pending_large_prime_slice` (`QSAG.OUTER.MULCHECK.FP.FOLD.V1`, `outer_mpc.rs:1946-1998`). -/
def fpFoldRound {F : Type} [CommRingOps F] (s : FpIpClaim F) (m : FpFoldMsg F) (rk : F) : FpIpClaim F where
  len := s.half
  a := fun k => if k < s.half then s.padA (2 * k) + rk * s.padA (2 * k + 1) else 0
  b := fun k => if k < s.half then rk * s.padB (2 * k) + s.padB (2 * k + 1) else 0
  c := m.d0 + rk * s.c + (rk * rk) * m.d1

private theorem fpDot_pairs_eq {F : Type} [LawfulCommRing F] (s : FpIpClaim F) :
    fpDot s.len s.a s.b =
      fpSum s.half (fun k => s.padA (2 * k) * s.padB (2 * k) + s.padA (2 * k + 1) * s.padB (2 * k + 1)) := by
  have hPairGen : ∀ n : Nat,
      fpDot n (fun i => if i < n then s.a i else 0) (fun i => if i < n then s.b i else 0) =
        fpSum ((n + 1) / 2) (fun k =>
          (if 2 * k < n then s.a (2 * k) else 0) * (if 2 * k < n then s.b (2 * k) else 0) +
          (if 2 * k + 1 < n then s.a (2 * k + 1) else 0) * (if 2 * k + 1 < n then s.b (2 * k + 1) else 0)) := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      rcases n with _ | _ | m
      · rfl
      · show (0 + (if 0 < 1 then s.a 0 else 0) * (if 0 < 1 then s.b 0 else 0)) =
          0 + ((if 0 < 1 then s.a 0 else 0) * (if 0 < 1 then s.b 0 else 0) +
               (if 1 < 1 then s.a 1 else 0) * (if 1 < 1 then s.b 1 else 0))
        simp only [Nat.zero_lt_one, Nat.lt_irrefl, ↓reduceIte]
        constructive_ring
      · have hHalf : (m + 2 + 1) / 2 = (m + 1) / 2 + 1 := by omega
        rw [hHalf]
        dsimp only [fpDot, fpSum]
        have hSub : fpDot m (fun i => if i < m + 2 then s.a i else 0)
                            (fun i => if i < m + 2 then s.b i else 0) =
            fpDot m (fun i => if i < m then s.a i else 0)
                    (fun i => if i < m then s.b i else 0) :=
          fpDot_congr m
            (fun i hi => by rw [cIte_pos (by omega : i < m + 2), cIte_pos hi])
            (fun i hi => by rw [cIte_pos (by omega : i < m + 2), cIte_pos hi])
        have hSumSub : ∀ h : Nat, h ≤ (m + 1) / 2 → (2 * h ≤ m →
            fpSum h (fun k =>
              (if 2 * k < m + 2 then s.a (2 * k) else 0) * (if 2 * k < m + 2 then s.b (2 * k) else 0) +
              (if 2 * k + 1 < m + 2 then s.a (2 * k + 1) else 0) * (if 2 * k + 1 < m + 2 then s.b (2 * k + 1) else 0)) =
            fpSum h (fun k =>
              (if 2 * k < m then s.a (2 * k) else 0) * (if 2 * k < m then s.b (2 * k) else 0) +
              (if 2 * k + 1 < m then s.a (2 * k + 1) else 0) * (if 2 * k + 1 < m then s.b (2 * k + 1) else 0))) := by
          intro h _ hBound
          induction h with
          | zero => rfl
          | succ h ihH =>
            dsimp only [fpSum]
            rw [ihH (by omega) (by omega)]
            simp only [show 2 * h < m + 2 from by omega, show 2 * h < m from by omega,
              show 2 * h + 1 < m + 2 from by omega, show 2 * h + 1 < m from by omega, ↓reduceIte]
        have hPar : m % 2 = 0 ∨ m % 2 = 1 := by omega
        rcases hPar with hEven | hOdd
        · obtain ⟨q, hmEq⟩ : ∃ q, m = 2 * q := ⟨m / 2, by omega⟩
          subst hmEq
          have hQ : (2 * q + 1) / 2 = q := by omega
          rw [hQ, hSub, ih (2 * q) (by omega), hQ,
              hSumSub q (by omega) (by omega)]
          simp only [show 2 * q < 2 * q + 2 from by omega,
            show 2 * q + 1 < 2 * q + 2 from by omega, ↓reduceIte]
          constructive_ring
        · obtain ⟨q, hmEq⟩ : ∃ q, m = 2 * q + 1 := ⟨m / 2, by omega⟩
          subst hmEq
          have hQ1 : (2 * q + 1 + 1) / 2 = q + 1 := by omega
          rw [hQ1, hSub, ih (2 * q + 1) (by omega), hQ1]
          dsimp only [fpSum]
          rw [hSumSub q (by omega) (by omega)]
          simp only [show 2 * q < 2 * q + 1 + 2 from by omega,
            show 2 * q < 2 * q + 1 from by omega,
            show 2 * q + 1 < 2 * q + 1 + 2 from by omega,
            show ¬ (2 * q + 1 < 2 * q + 1) from Nat.lt_irrefl _,
            show 2 * (q + 1) = 2 * q + 1 + 1 from by omega,
            show 2 * q + 1 + 1 < 2 * q + 1 + 2 from by omega,
            show ¬ (2 * q + 1 + 2 < 2 * q + 1 + 2) from Nat.lt_irrefl _, ↓reduceIte]
          constructive_ring
  have hDotSelf : fpDot s.len s.a s.b =
      fpDot s.len (fun i => if i < s.len then s.a i else 0) (fun i => if i < s.len then s.b i else 0) :=
    fpDot_congr s.len (fun i hi => (cIte_pos hi (s.a i) 0).symm)
      (fun i hi => (cIte_pos hi (s.b i) 0).symm)
  rw [hDotSelf, hPairGen s.len]
  rfl

/-- Exact quadratic polynomial error law for `fpFoldRound`. -/
theorem fpFoldRound_err {F : Type} [LawfulCommRing F] (s : FpIpClaim F) (m : FpFoldMsg F) (rk : F) :
    (fpFoldRound s m rk).err =
      RoundPoly.evalCoeffs [s.crossLoHi - m.d0, s.err, s.crossHiLo - m.d1] rk := by
  unfold FpIpClaim.err fpFoldRound FpIpClaim.crossLoHi FpIpClaim.crossHiLo
  dsimp only
  rw [fpDot_pairs_eq s]
  have hDotExpand : ∀ h : Nat, h ≤ s.half →
      fpDot h (fun k => if k < s.half then s.padA (2 * k) + rk * s.padA (2 * k + 1) else 0)
              (fun k => if k < s.half then rk * s.padB (2 * k) + s.padB (2 * k + 1) else 0) =
      fpSum h (fun k => s.padA (2 * k) * s.padB (2 * k + 1)) +
        rk * fpSum h (fun k => s.padA (2 * k) * s.padB (2 * k) + s.padA (2 * k + 1) * s.padB (2 * k + 1)) +
        (rk * rk) * fpSum h (fun k => s.padA (2 * k + 1) * s.padB (2 * k)) := by
    intro h hh
    induction h with
    | zero =>
      dsimp only [fpDot, fpSum]
      constructive_ring
    | succ h ih =>
      have hhLt : h < s.half := by omega
      dsimp only [fpDot, fpSum]
      rw [cIte_pos hhLt, cIte_pos hhLt, ih (by omega)]
      constructive_ring
  rw [hDotExpand s.half (Nat.le_refl s.half)]
  dsimp only [RoundPoly.evalCoeffs]
  constructive_ring

/-- **Step-2 Fold-Round Soundness (`fpFoldRound_false_claim_survives_at_most_two_coins`)**:
    Over every domain `F`, a false inner-product claim (`s.err ≠ 0`) survives `fpFoldRound` on at
    most `2` challenges `rk ∈ S`! -/
theorem fpFoldRound_false_claim_survives_at_most_two_coins
    {F : Type} [LawfulCommRing F] [DecidableEq F] [NoZeroDivisors F]
    (s : FpIpClaim F) (m : FpFoldMsg F) (hErr : s.err ≠ 0)
    (S : List F) (hS : S.Nodup) :
    (S.filter (fun rk => decide ((fpFoldRound s m rk).err = 0))).length ≤ 2 := by
  let cs : List F := [s.crossLoHi - m.d0, s.err, s.crossHiLo - m.d1]
  have hEx : ∃ c ∈ cs, c ≠ CommRingOps.zero :=
    ⟨s.err, List.Mem.tail _ (List.Mem.head _), hErr⟩
  exact gs_formal_root_bound 2 cs
    (S.filter (fun rk => decide ((fpFoldRound s m rk).err = 0)))
    (Nat.le_refl 3) hEx (hS.filter _)
    (fun rk hMem => by
      have hDec := (List.mem_filter.mp hMem).2
      rw [← fpFoldRound_err s m rk]
      exact of_decide_eq_true hDec)

/-- Base-case masks and cross-terms `(u, v, d1, d2)` (`outer_mpc.rs:2005-2017`). -/
structure FpBaseMsg (F : Type) where
  u : F
  v : F
  d1 : F
  d2 : F

/-- Step 3 of `verify_pending_large_prime_slice` (`QSAG.OUTER.MULCHECK.FP.BASE.V1`, `outer_mpc.rs:2038-2055`). -/
def fpBaseAccepts {F : Type} [CommRingOps F] [DecidableEq F]
    (s : FpIpClaim F) (m : FpBaseMsg F) (rb : F) : Bool :=
  decide (s.len = 1) &&
    decide (s.c + m.d1 * rb + m.d2 * (rb * rb) = (s.a 0 + m.u * rb) * (s.b 0 + m.v * rb))

/-- **Step-3 Base-Sacrifice Soundness (`fpBaseAccepts_false_claim_at_most_two_coins`)**:
    Over every domain `F`, a false single-pair claim (`s.err ≠ 0`) passes `fpBaseAccepts` on at
    most `2` base coins `rb ∈ Sb`! -/
theorem fpBaseAccepts_false_claim_at_most_two_coins
    {F : Type} [LawfulCommRing F] [DecidableEq F] [NoZeroDivisors F]
    (s : FpIpClaim F) (m : FpBaseMsg F) (hErr : s.err ≠ 0)
    (Sb : List F) (hSb : Sb.Nodup) :
    (Sb.filter (fpBaseAccepts s m)).length ≤ 2 := by
  by_cases hLen : s.len = 1
  · let cs : List F := [s.err, (s.a 0 * m.v + m.u * s.b 0) - m.d1, m.u * m.v - m.d2]
    have hEx : ∃ c ∈ cs, c ≠ CommRingOps.zero := ⟨s.err, List.Mem.head _, hErr⟩
    have hErr1 : s.err = s.a 0 * s.b 0 - s.c := by
      unfold FpIpClaim.err
      rw [hLen]
      dsimp only [fpDot]
      constructive_ring
    exact gs_formal_root_bound 2 cs (Sb.filter (fpBaseAccepts s m))
      (Nat.le_refl 3) hEx (hSb.filter _)
      (fun rb hMem => by
        have hAcc := (List.mem_filter.mp hMem).2
        unfold fpBaseAccepts at hAcc
        rw [Bool.and_eq_true] at hAcc
        have hEq := of_decide_eq_true hAcc.2
        have hDiff : RoundPoly.evalCoeffs cs rb =
            (s.a 0 + m.u * rb) * (s.b 0 + m.v * rb) -
            (s.c + m.d1 * rb + m.d2 * (rb * rb)) := by
          dsimp only [cs, RoundPoly.evalCoeffs]
          rw [hErr1]
          constructive_ring
        rw [hDiff, ← hEq]
        show (s.c + m.d1 * rb + m.d2 * (rb * rb)) -
            (s.c + m.d1 * rb + m.d2 * (rb * rb)) = 0
        constructive_ring)
  · have hEmpty : (Sb.filter (fpBaseAccepts s m)).length = 0 := by
      have hFalse : fpBaseAccepts s m = fun _ => false := by
        funext rb
        unfold fpBaseAccepts
        rw [decide_eq_false hLen, Bool.false_and]
      rw [hFalse]
      exact filter_false_length Sb
    rw [hEmpty]
    decide

/-- Adaptive prover for `r` prime-field halving rounds + base sacrifice (`9/12` `@[expose]`). -/
@[expose] def FpFoldProver (F : Type) : Nat → Type
  | 0 => FpBaseMsg F
  | r + 1 => FpFoldMsg F × (F → FpFoldProver F r)

def fpSacrificeAccepts {F : Type} [CommRingOps F] [DecidableEq F] :
    (r : Nat) → FpFoldProver F r → FpIpClaim F → List F → Bool
  | 0, bm, s, [rb] => fpBaseAccepts s bm rb
  | 0, _, _, _ => false
  | _ + 1, _, _, [] => false
  | r + 1, p, s, rk :: rest => fpSacrificeAccepts r (p.2 rk) (fpFoldRound s p.1 rk) rest

def fpCoinVectors {F : Type} (S Sb : List F) : Nat → List (List F)
  | 0 => Sb.map (fun rb => [rb])
  | r + 1 => S.flatMap (fun rk => (fpCoinVectors S Sb r).map (fun rest => rk :: rest))

theorem fpCoinVectors_length {F : Type} (S Sb : List F) :
    ∀ r, (fpCoinVectors S Sb r).length = S.length ^ r * Sb.length
  | 0 => by show (Sb.map _).length = S.length ^ 0 * Sb.length; rw [List.length_map, Nat.pow_zero, Nat.one_mul]
  | r + 1 => by
    show (S.flatMap (fun rk => (fpCoinVectors S Sb r).map (fun rest => rk :: rest))).length = _
    rw [flatMap_map_length (fpCoinVectors S Sb r) (fun rk rest => rk :: rest) S,
        fpCoinVectors_length S Sb r, Nat.pow_succ, Nat.mul_comm (S.length ^ r) S.length, Nat.mul_assoc]

theorem fpSacrifice_false_claim_accepting_coins_bound
    {F : Type} [LawfulCommRing F] [DecidableEq F] [NoZeroDivisors F]
    (S Sb : List F) (hS : S.Nodup) (hSb : Sb.Nodup) :
    ∀ (r : Nat) (p : FpFoldProver F r) (s : FpIpClaim F), s.err ≠ 0 →
      ((fpCoinVectors S Sb r).filter (fpSacrificeAccepts r p s)).length ≤
        sacrificeBadCoinBound S.length Sb.length r
  | 0, bm, s, hErr => by
    show ((Sb.map (fun rb => [rb])).filter (fpSacrificeAccepts 0 bm s)).length ≤ 2
    rw [filter_map_length]
    exact fpBaseAccepts_false_claim_at_most_two_coins s bm hErr Sb hSb
  | r + 1, p, s, hErr => by
    show ((S.flatMap (fun rk => (fpCoinVectors S Sb r).map (fun rest => rk :: rest))).filter
      (fpSacrificeAccepts (r + 1) p s)).length ≤
      2 * (S.length ^ r * Sb.length) + S.length * sacrificeBadCoinBound S.length Sb.length r
    rw [filter_flatMap_length]
    have hMapEq : (S.map (fun rk =>
        (((fpCoinVectors S Sb r).map (fun rest => rk :: rest)).filter
          (fpSacrificeAccepts (r + 1) p s)).length)) =
        (S.map (fun rk =>
          ((fpCoinVectors S Sb r).filter
            (fpSacrificeAccepts r (p.2 rk) (fpFoldRound s p.1 rk))).length)) := by
      apply List.map_congr_left
      intro rk _
      rw [filter_map_length]
      rfl
    rw [hMapEq]
    have hSplit := sum_map_le_split
      (fun rk => decide ((fpFoldRound s p.1 rk).err = 0))
      (fun rk => ((fpCoinVectors S Sb r).filter
        (fpSacrificeAccepts r (p.2 rk) (fpFoldRound s p.1 rk))).length)
      (S.length ^ r * Sb.length) (sacrificeBadCoinBound S.length Sb.length r)
      (fun rk => by rw [← fpCoinVectors_length S Sb r]; exact List.length_filter_le _ _)
      (fun rk hg => fpSacrifice_false_claim_accepting_coins_bound S Sb hS hSb r (p.2 rk)
        (fpFoldRound s p.1 rk) (of_decide_eq_false hg)) S
    have hBad := fpFoldRound_false_claim_survives_at_most_two_coins s p.1 hErr S hS
    have hMul := Nat.mul_le_mul_right (S.length ^ r * Sb.length) hBad
    omega

/-- Adaptive prover for the complete prime-field flush (`RLC` + `r` halvings + base sacrifice). -/
structure FpCheckProver (F : Type) (r : Nat) where
  afterRlc : F → FpFoldProver F r

def fpFieldCheckAccepts {F : Type} [CommRingOps F] [DecidableEq F]
    (r N iStar : Nat) (triples : Nat → FpTriple F) (otherChis : Nat → F)
    (p : FpCheckProver F r) : List F → Bool
  | [] => false
  | chi :: rest =>
    fpSacrificeAccepts r (p.afterRlc chi) (fpRlcClaim N triples (setFpChiAt otherChis iStar chi)) rest

def fpFieldCheckCoins {F : Type} (S Sb : List F) (r : Nat) : List (List F) :=
  S.flatMap (fun chi => (fpCoinVectors S Sb r).map (fun rest => chi :: rest))

theorem fpFieldCheckCoins_length {F : Type} (S Sb : List F) (r : Nat) :
    (fpFieldCheckCoins S Sb r).length = S.length ^ (r + 1) * Sb.length := by
  unfold fpFieldCheckCoins
  rw [flatMap_map_length (fpCoinVectors S Sb r) (fun chi rest => chi :: rest) S,
      fpCoinVectors_length S Sb r, Nat.pow_succ, Nat.mul_comm (S.length ^ r) S.length, Nat.mul_assoc]

/-- Total bad-coin count for `verify_pending_large_prime_slice`: `1` RLC coin + `2r` fold coins + `2` base coins. -/
def fieldCheckBadCoinBound (n nb r : Nat) : Nat :=
  1 * (n ^ r * nb) + n * sacrificeBadCoinBound n nb r

/-- **Full Prime-Field Flush Soundness (`fpFieldCheck_false_triple_accepting_coins_bound`)**:
    Over any domain `F`, if triple `iStar < N` has `(triples iStar).defect ≠ 0`, then for ANY
    adaptive prover `p : FpCheckProver F r`, the number of accepting `(chi, rk_1..rk_r, rb)` coin
    vectors in `fpFieldCheckCoins S Sb r` is at most `fieldCheckBadCoinBound S.length Sb.length r`! -/
theorem fpFieldCheck_false_triple_accepting_coins_bound
    {F : Type} [LawfulCommRing F] [DecidableEq F] [NoZeroDivisors F]
    (S Sb : List F) (hS : S.Nodup) (hSb : Sb.Nodup)
    (r N iStar : Nat) (triples : Nat → FpTriple F)
    (hi : iStar < N) (hDefNe : (triples iStar).defect ≠ 0)
    (otherChis : Nat → F) (p : FpCheckProver F r) :
    ((fpFieldCheckCoins S Sb r).filter
      (fpFieldCheckAccepts r N iStar triples otherChis p)).length ≤
      fieldCheckBadCoinBound S.length Sb.length r := by
  unfold fpFieldCheckCoins fieldCheckBadCoinBound
  rw [filter_flatMap_length]
  have hMapEq : (S.map (fun chi =>
      (((fpCoinVectors S Sb r).map (fun rest => chi :: rest)).filter
        (fpFieldCheckAccepts r N iStar triples otherChis p)).length)) =
      (S.map (fun chi =>
        ((fpCoinVectors S Sb r).filter
          (fpSacrificeAccepts r (p.afterRlc chi)
            (fpRlcClaim N triples (setFpChiAt otherChis iStar chi)))).length)) := by
    apply List.map_congr_left
    intro chi _
    rw [filter_map_length]
    rfl
  rw [hMapEq]
  have hSplit := sum_map_le_split
    (fun chi => decide ((fpRlcClaim N triples (setFpChiAt otherChis iStar chi)).err = 0))
    (fun chi => ((fpCoinVectors S Sb r).filter
      (fpSacrificeAccepts r (p.afterRlc chi)
        (fpRlcClaim N triples (setFpChiAt otherChis iStar chi)))).length)
    (S.length ^ r * Sb.length) (sacrificeBadCoinBound S.length Sb.length r)
    (fun chi => by rw [← fpCoinVectors_length S Sb r]; exact List.length_filter_le _ _)
    (fun chi hg => fpSacrifice_false_claim_accepting_coins_bound S Sb hS hSb r (p.afterRlc chi)
      (fpRlcClaim N triples (setFpChiAt otherChis iStar chi)) (of_decide_eq_false hg)) S
  have hBad := fpRlc_false_triple_survives_at_most_one_coin N iStar triples hi hDefNe otherChis S hS
  have hMul := Nat.mul_le_mul_right (S.length ^ r * Sb.length) hBad
  omega

end PrimeFieldCheck

/-- Closed form for `fieldCheckBadCoinBound`:
    `fieldCheckBadCoinBound M (M - 1) r * (M - 1) ≤ (1 + 2 * r + 2) * (M ^ (r + 1) * (M - 1))`. -/
theorem fieldCheckBadCoinBound_closed_le (M r : Nat) :
    fieldCheckBadCoinBound M (M - 1) r * (M - 1) ≤
      (1 + 2 * r + 2) * (M ^ (r + 1) * (M - 1)) := by
  unfold fieldCheckBadCoinBound
  have hClosed : M * sacrificeBadCoinBound M (M - 1) r =
      2 * r * (M ^ r * (M - 1)) + 2 * M ^ (r + 1) := by
    rw [Nat.mul_comm M _, sacrificeBadCoinBound_closed M (M - 1) r]
  rw [hClosed]
  have hSubLe : M - 1 ≤ M := Nat.sub_le M 1
  have hTerm1 : 1 * (M ^ r * (M - 1)) * (M - 1) ≤ 1 * (M ^ (r + 1) * (M - 1)) := by
    rw [Nat.one_mul, Nat.one_mul, Nat.pow_succ]
    have hAssoc : M ^ r * (M - 1) * (M - 1) = M ^ r * (M - 1) * (M - 1) := rfl
    have hRhs : M ^ r * M * (M - 1) = M ^ r * (M - 1) * M := by
      rw [Nat.mul_assoc, Nat.mul_comm M (M - 1), ← Nat.mul_assoc]
    rw [hRhs]
    exact Nat.mul_le_mul_left (M ^ r * (M - 1)) hSubLe
  have hTerm2 : (2 * r * (M ^ r * (M - 1)) + 2 * M ^ (r + 1)) * (M - 1) ≤
      (2 * r + 2) * (M ^ (r + 1) * (M - 1)) := by
    rw [Nat.add_mul, Nat.add_mul]
    apply Nat.add_le_add
    · have hL : 2 * r * (M ^ r * (M - 1)) * (M - 1) =
          2 * r * (M ^ r * (M - 1) * (M - 1)) := by rw [Nat.mul_assoc]
      have hR : 2 * r * (M ^ (r + 1) * (M - 1)) =
          2 * r * (M ^ r * (M - 1) * M) := by
        rw [Nat.pow_succ, Nat.mul_assoc (M ^ r) M (M - 1),
            Nat.mul_comm M (M - 1), ← Nat.mul_assoc (M ^ r) (M - 1) M]
      rw [hL, hR]
      exact Nat.mul_le_mul_left (2 * r) (Nat.mul_le_mul_left (M ^ r * (M - 1)) hSubLe)
    · rw [Nat.mul_assoc 2 (M ^ (r + 1)) (M - 1)]
      exact Nat.le_refl _
  rw [Nat.add_mul]
  have hSum := Nat.add_le_add hTerm1 hTerm2
  have hRhsEq : 1 * (M ^ (r + 1) * (M - 1)) + (2 * r + 2) * (M ^ (r + 1) * (M - 1)) =
      (1 + 2 * r + 2) * (M ^ (r + 1) * (M - 1)) := by
    rw [← Nat.add_mul, Nat.add_assoc]
  exact hRhsEq ▸ hSum

/-- **`FIELD_CHECK_NUMERATOR = 35` Soundness (`field_check_numerator_35_bound`)**:
    1. `MAX_PENDING_FIELD_WORDS * 64 = 1024 * 64 = 2^16` (`FIELD_CHECK_HALVING_ROUNDS = 16`),
    2. `1 + 2 * FIELD_CHECK_HALVING_ROUNDS + 2 = 35 = FIELD_CHECK_NUMERATOR`,
    3. For EVERY prime modulus `p`, `fieldCheckBadCoinBound p (p - 1) 16 * (p - 1) ≤ 35 * (p^17 * (p - 1))`,
    4. For EVERY large curve prime `p ≥ 2^254 + 1` (`Secp256k1`, `Ed25519`, `PallasFp`, `BlsFp`),
       `fieldCheckBadCoinBound p (p - 1) 16 * 2^248 ≤ p^17 * (p - 1)` (`< 2^-248`)! -/
theorem field_check_numerator_35_bound :
    MAX_PENDING_FIELD_WORDS * 64 = 2 ^ FIELD_CHECK_HALVING_ROUNDS ∧
    1 + 2 * FIELD_CHECK_HALVING_ROUNDS + 2 = FIELD_CHECK_NUMERATOR ∧
    FIELD_CHECK_NUMERATOR = 35 ∧
    (∀ p : Nat,
      fieldCheckBadCoinBound p (p - 1) FIELD_CHECK_HALVING_ROUNDS * (p - 1) ≤
        FIELD_CHECK_NUMERATOR * (p ^ (FIELD_CHECK_HALVING_ROUNDS + 1) * (p - 1))) ∧
    (∀ p : Nat, 2 ^ 254 + 1 ≤ p →
      fieldCheckBadCoinBound p (p - 1) FIELD_CHECK_HALVING_ROUNDS * 2 ^ 248 ≤
        p ^ (FIELD_CHECK_HALVING_ROUNDS + 1) * (p - 1)) := by
  refine ⟨by decide, by decide, rfl, ?_, ?_⟩
  · intro p
    exact fieldCheckBadCoinBound_closed_le p FIELD_CHECK_HALVING_ROUNDS
  · intro p hp
    have h35le : FIELD_CHECK_NUMERATOR * 2 ^ 248 ≤ p - 1 := by
      have h35le64 : FIELD_CHECK_NUMERATOR ≤ 2 ^ 6 := by decide
      have hConst : FIELD_CHECK_NUMERATOR * 2 ^ 248 ≤ 2 ^ 254 := by
        calc FIELD_CHECK_NUMERATOR * 2 ^ 248
            ≤ 2 ^ 6 * 2 ^ 248 := Nat.mul_le_mul_right _ h35le64
          _ = 2 ^ (6 + 248) := (Nat.pow_add 2 6 248).symm
      have hSub : 2 ^ 254 ≤ p - 1 := Nat.le_sub_of_add_le hp
      exact Nat.le_trans hConst hSub
    have hBase := fieldCheckBadCoinBound_closed_le p FIELD_CHECK_HALVING_ROUNDS
    have h35Eq : 1 + 2 * FIELD_CHECK_HALVING_ROUNDS + 2 = FIELD_CHECK_NUMERATOR := by decide
    rw [h35Eq] at hBase
    have hp1Pos : 0 < p - 1 :=
      Nat.lt_of_lt_of_le (Nat.two_pow_pos 254) (Nat.le_sub_of_add_le hp)
    have hScaled :
        (fieldCheckBadCoinBound p (p - 1) FIELD_CHECK_HALVING_ROUNDS * 2 ^ 248) * (p - 1) ≤
          (p ^ (FIELD_CHECK_HALVING_ROUNDS + 1) * (p - 1)) * (p - 1) := by
      calc (fieldCheckBadCoinBound p (p - 1) FIELD_CHECK_HALVING_ROUNDS * 2 ^ 248) * (p - 1)
          = (fieldCheckBadCoinBound p (p - 1) FIELD_CHECK_HALVING_ROUNDS * (p - 1)) * 2 ^ 248 := by
            rw [Nat.mul_assoc, Nat.mul_comm (2 ^ 248) (p - 1), ← Nat.mul_assoc]
        _ ≤ (FIELD_CHECK_NUMERATOR * (p ^ (FIELD_CHECK_HALVING_ROUNDS + 1) * (p - 1))) * 2 ^ 248 :=
            Nat.mul_le_mul_right (2 ^ 248) hBase
        _ = (FIELD_CHECK_NUMERATOR * 2 ^ 248) * (p ^ (FIELD_CHECK_HALVING_ROUNDS + 1) * (p - 1)) := by
            rw [Nat.mul_assoc, Nat.mul_comm (p ^ (FIELD_CHECK_HALVING_ROUNDS + 1) * (p - 1)) (2 ^ 248),
                ← Nat.mul_assoc]
        _ ≤ (p - 1) * (p ^ (FIELD_CHECK_HALVING_ROUNDS + 1) * (p - 1)) :=
            Nat.mul_le_mul_right _ h35le
        _ = (p ^ (FIELD_CHECK_HALVING_ROUNDS + 1) * (p - 1)) * (p - 1) :=
            Nat.mul_comm _ _
    exact Nat.le_of_mul_le_mul_right hScaled hp1Pos

/-- `#tooth` Tightness of `FIELD_CHECK_NUMERATOR = 35`: replacing `35` by `34` is strictly violated
    at every modulus `p ≥ 34` (in particular every curve prime `p ≥ 2^254 + 1`)! -/
theorem tooth_field_check_numerator_34_too_small (p : Nat) (hp : 34 ≤ p) :
    ¬ (fieldCheckBadCoinBound p (p - 1) FIELD_CHECK_HALVING_ROUNDS * (p - 1) ≤
      34 * (p ^ (FIELD_CHECK_HALVING_ROUNDS + 1) * (p - 1))) := by
  intro hLe
  have hClosed : p * sacrificeBadCoinBound p (p - 1) 16 =
      32 * (p ^ 16 * (p - 1)) + 2 * p ^ 17 := by
    rw [Nat.mul_comm p _, sacrificeBadCoinBound_closed p (p - 1) 16]
  change (1 * (p ^ 16 * (p - 1)) + p * sacrificeBadCoinBound p (p - 1) 16) * (p - 1) ≤
    34 * (p ^ 17 * (p - 1)) at hLe
  rw [hClosed] at hLe
  have hp16Pos : 0 < p ^ 16 := Nat.pow_pos (by omega : 0 < p)
  have hBasePos : 0 < p ^ 16 * (p - 1) := Nat.mul_pos hp16Pos (by omega)
  have hP17 : p ^ 17 = p * p ^ 16 := (Nat.pow_succ p 16).trans (Nat.mul_comm _ _)
  have hLhsEq :
      (1 * (p ^ 16 * (p - 1)) + (32 * (p ^ 16 * (p - 1)) + 2 * p ^ 17)) * (p - 1) =
      (33 * (p - 1) + 2 * p) * (p ^ 16 * (p - 1)) := by
    rw [hP17, Nat.add_mul, Nat.add_mul, Nat.add_mul]
    have e1 : 1 * (p ^ 16 * (p - 1)) * (p - 1) = (p - 1) * (p ^ 16 * (p - 1)) := by
      rw [Nat.one_mul, Nat.mul_comm]
    have e2 : 32 * (p ^ 16 * (p - 1)) * (p - 1) = 32 * (p - 1) * (p ^ 16 * (p - 1)) := by
      rw [Nat.mul_assoc, Nat.mul_comm (p ^ 16 * (p - 1)) (p - 1), ← Nat.mul_assoc]
    have e3 : 2 * (p * p ^ 16) * (p - 1) = 2 * p * (p ^ 16 * (p - 1)) := by
      rw [← Nat.mul_assoc 2 p (p ^ 16), Nat.mul_assoc (2 * p) (p ^ 16) (p - 1)]
    rw [e1, e2, e3]
    have e4 : (p - 1) * (p ^ 16 * (p - 1)) + 32 * (p - 1) * (p ^ 16 * (p - 1)) =
        33 * (p - 1) * (p ^ 16 * (p - 1)) := by
      have h1 : (p - 1) * (p ^ 16 * (p - 1)) = 1 * ((p - 1) * (p ^ 16 * (p - 1))) :=
        (Nat.one_mul _).symm
      conv => lhs; lhs; rw [h1]
      rw [Nat.mul_assoc 32 (p - 1) _, ← Nat.add_mul 1 32 _, ← Nat.mul_assoc]
    rw [← Nat.add_assoc, e4]
  have hRhsEq : 34 * (p ^ 17 * (p - 1)) = (34 * p) * (p ^ 16 * (p - 1)) := by
    rw [hP17, Nat.mul_assoc p (p ^ 16) (p - 1), ← Nat.mul_assoc 34 p _]
  rw [hLhsEq, hRhsEq] at hLe
  have hCoeffLe : 33 * (p - 1) + 2 * p ≤ 34 * p :=
    Nat.le_of_mul_le_mul_right hLe hBasePos
  omega

#tooth_pair Qsag.MigrationExecution.field_check_numerator_35_bound vs
  Qsag.MigrationExecution.tooth_field_check_numerator_34_too_small

set_option exponentiation.threshold 512 in
/-- **438-Repetition ZKBoo + Active-Flush QROM Fiat–Shamir Soundness
    (`migration_438_zkboo_and_ceremony_qrom_soundness`)**:
    1. Every repetition without a `PendingAnd` fault evaluates to `false` on a false witness, so at
       least 1 of the 3 ZKBoo custodian-pair views rejects (`≤ 2 / 3` per repetition; across 438
       repetitions, `8 * (qHash + 1)^2 * 2^438 * 2^128 ≤ 3^438` for all `qHash + 1 ≤ 2^56`),
    2. Classical Fiat–Shamir ceiling `(qHash + 1) * 2^438 * 2^192 ≤ 3^438`,
    3. Production Boolean active-MPC check `BIT_CHECK_NUMERATOR = 63` (`D0_BITS = 19`:
       `1 + 36 + 2 * 12 + 2 = 63`, and staged ternary sumcheck: `7 + 3 * 6 + 2 * 18 + 2 = 63`,
       `< 2^-244` across two lockstep instances),
    4. Production prime-field active-MPC check `FIELD_CHECK_NUMERATOR = 35` (`1 + 2 * 16 + 2 = 35`,
       `≤ 35 / (p - 1) < 2^-248` for all curve primes `p ≥ 2^254 + 1`)! -/
theorem migration_438_zkboo_and_ceremony_qrom_soundness
    (qHash : Nat) (hqHash : qHash + 1 ≤ 2 ^ 56) :
    8 * (qHash + 1) ^ 2 * 2 ^ 438 * 2 ^ 128 ≤ 3 ^ 438 ∧
    (qHash + 1) * 2 ^ 438 * 2 ^ 192 ≤ 3 ^ 438 ∧
    (BIT_CHECK_NUMERATOR = 63 ∧
     (1 * ((2 ^ 128) ^ 13 * (2 ^ 128 - 1)) +
        2 ^ 128 * round0D19SacrificeBadBound (2 ^ 128) (2 ^ 128 - 1) 12) * (2 ^ 128 - 1) ≤
       BIT_CHECK_NUMERATOR * ((2 ^ 128) ^ 14 * (2 ^ 128 - 1)) ∧
     stagedBadCoinBound (2 ^ 128) ((2 ^ 128) ^ rustBitCheckHalvingRounds * (2 ^ 128 - 1))
         (sacrificeBadCoinBound (2 ^ 128) (2 ^ 128 - 1) rustBitCheckHalvingRounds)
         rustBitCheckStageNumerators * (2 ^ 128 - 1) ≤
       BIT_CHECK_NUMERATOR * ((2 ^ 128) ^ rustBitCheckStageNumerators.length *
         ((2 ^ 128) ^ rustBitCheckHalvingRounds * (2 ^ 128 - 1)))) ∧
    (FIELD_CHECK_NUMERATOR = 35 ∧
     ∀ p : Nat, 2 ^ 254 + 1 ≤ p →
       fieldCheckBadCoinBound p (p - 1) FIELD_CHECK_HALVING_ROUNDS * (p - 1) ≤
         FIELD_CHECK_NUMERATOR * (p ^ (FIELD_CHECK_HALVING_ROUNDS + 1) * (p - 1)) ∧
       fieldCheckBadCoinBound p (p - 1) FIELD_CHECK_HALVING_ROUNDS * 2 ^ 248 ≤
         p ^ (FIELD_CHECK_HALVING_ROUNDS + 1) * (p - 1)) := by
  have h3gt : 2 ^ 438 * 2 ^ 256 ≤ 3 ^ 438 := by decide +kernel
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hSq : (qHash + 1) ^ 2 ≤ 2 ^ 112 := by
      have p1 := Nat.pow_le_pow_left hqHash 2
      have p2 : (2 ^ 56) ^ 2 = 2 ^ 112 := by decide
      rw [p2] at p1; exact p1
    have h8 : 8 * (qHash + 1) ^ 2 ≤ 2 ^ 115 := by
      have p1 := Nat.mul_le_mul_left 8 hSq
      have p2 : 8 * 2 ^ 112 = 2 ^ 115 := by decide
      rw [p2] at p1; exact p1
    have hm := Nat.mul_le_mul_right (2 ^ 438 * 2 ^ 128) h8
    have hLhs : 8 * (qHash + 1) ^ 2 * 2 ^ 438 * 2 ^ 128 =
        8 * (qHash + 1) ^ 2 * (2 ^ 438 * 2 ^ 128) := by simp only [Nat.mul_assoc]
    have hRhs : 2 ^ 115 * (2 ^ 438 * 2 ^ 128) ≤ 2 ^ 438 * 2 ^ 256 := by
      have p : 2 ^ 115 * (2 ^ 438 * 2 ^ 128) = 2 ^ 438 * (2 ^ 115 * 2 ^ 128) := by
        rw [← Nat.mul_assoc, Nat.mul_comm (2 ^ 115) (2 ^ 438), Nat.mul_assoc]
      rw [p, ← Nat.pow_add]
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide : 0 < 2) (by decide : 243 ≤ 256))
    rw [hLhs]
    exact Nat.le_trans hm (Nat.le_trans hRhs h3gt)
  · have hm := Nat.mul_le_mul_right (2 ^ 438 * 2 ^ 192) hqHash
    have hLhs : (qHash + 1) * 2 ^ 438 * 2 ^ 192 =
        (qHash + 1) * (2 ^ 438 * 2 ^ 192) := by simp only [Nat.mul_assoc]
    have hRhs : 2 ^ 56 * (2 ^ 438 * 2 ^ 192) ≤ 2 ^ 438 * 2 ^ 256 := by
      have p : 2 ^ 56 * (2 ^ 438 * 2 ^ 192) = 2 ^ 438 * (2 ^ 56 * 2 ^ 192) := by
        rw [← Nat.mul_assoc, Nat.mul_comm (2 ^ 56) (2 ^ 438), Nat.mul_assoc]
      rw [p, ← Nat.pow_add]
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide : 0 < 2) (by decide : 248 ≤ 256))
    rw [hLhs]
    exact Nat.le_trans hm (Nat.le_trans hRhs h3gt)
  · exact ⟨rfl, d19_round0_sacrifice_bit_check_63_bound.1,
      rust_bit_check_numerator_63_bound.2.2.1⟩
  · refine ⟨rfl, fun p hp => ⟨field_check_numerator_35_bound.2.2.2.1 p,
      field_check_numerator_35_bound.2.2.2.2 p hp⟩⟩

/-- Concrete inhabitedness witness for `migration_unconditional_circuit_to_sacrifice_ceremony_bound`:
    single-gate bit-0 check circuit `[.and 0 0 onesSh]` (`relB w := w.getLsbD 0`), consistent 7-fork
    all-zero witness `0#256` (`relB 0#256 = false`), corrupted output `onesSh` opening `true` in all
    64 lanes, and coin-oblivious `FullCeremonyProver 11`! -/
theorem inhabited_unconditional_circuit_to_sacrifice_ceremony :
    ∃ (gates : List Gate) (relB : MigrationKey256 → Bool)
      (batches : MigrationWitnessBatches) (st : Fin 7 → GateState)
      (numSuper : Fin 7 → Nat) (_otherGammas : Fin 7 → Nat → RustGf128)
      (p : FullCeremonyProver 11),
      CircuitSoundForRel gates relB ∧
      MigrationBatchConsistent batches ∧
      relB (extractRepetitionWitness (batches 0) 0) = false ∧
      (∀ b : Fin 7, evalGates ⟨witnessWires (batches b), []⟩ gates = some (st b)) ∧
      (∀ b : Fin 7, finishWithoutCheck (st b) = .accepted) ∧
      (∀ b : Fin 7, (st b).pending.length ≤ 128 * numSuper b) ∧
      11 ≤ 13 ∧
      FullForkStrategiesPrecedeOwnCoins p := by
  let onesSh : RssWord64Shares3 := ⟨0xFFFFFFFFFFFFFFFF, 0, 0⟩
  let zeroSh : RssWord64Shares3 := ⟨0, 0, 0⟩
  let gates : List Gate := [.and 0 0 onesSh]
  let relB : MigrationKey256 → Bool := fun w => w.getLsbD 0
  let wl : RssWitnessLanes3 := ⟨fun _ => 0, fun _ => 0, fun _ => 0⟩
  let batches : MigrationWitnessBatches := fun _ => wl
  let stVal : GateState := ⟨onesSh :: witnessWires wl, [⟨zeroSh, zeroSh, onesSh⟩]⟩
  have hCirc : CircuitSoundForRel gates relB := by
    intro w rest hEv
    simp only [gates, evalGatesBool, evalGateBool, List.getElem?_ofFn, Nat.zero_lt_succ,
      ↓reduceDIte, Bool.and_self, Option.bind_some] at hEv
    injection hEv with hCons
    exact (List.cons.inj hCons).1
  have hUnif : shareUniformLanesCheck wl = true := by
    unfold shareUniformLanesCheck wl
    apply (finAll_eq_true_iff 256 _).mpr
    intro _
    show (isUniformLaneWord 0 && isUniformLaneWord 0 && isUniformLaneWord 0) = true
    decide
  have hFalse : relB (extractRepetitionWitness wl 0) = false := by
    unfold relB extractRepetitionWitness wl
    rw [packBits_getLsbD 256 _ 0 (by decide)]
    decide
  have hW0 : (witnessWires wl)[0]? = some zeroSh := by
    unfold witnessWires wl
    rw [List.getElem?_ofFn]
    rfl
  have hEval : evalGates ⟨witnessWires wl, []⟩ gates = some stVal := by
    simp only [gates, evalGates, evalGate, hW0, Bind.bind, Pure.pure, Option.bind]
    rfl
  have hOpen : finishWithoutCheck stVal = .accepted := by
    unfold finishWithoutCheck stVal RssWord64Shares3.reconstruct onesSh
    decide
  have hCap1 : stVal.pending.length ≤ 128 * 1 := by
    show [PendingAnd.mk zeroSh zeroSh onesSh].length ≤ 128 * 1
    decide
  refine ⟨gates, relB, batches, fun _ => stVal, fun _ => 1, fun _ _ => 0#128,
    fun _ _ => ⟨fun _ _ _ => 0#128, fun _ => constFlushProver ⟨0#128, 0#128⟩ ⟨0#128, 0#128, 0#128, 0#128⟩ 11⟩,
    hCirc, ⟨fun _ => hUnif, fun _ => rfl⟩, hFalse, fun _ => hEval, fun _ => hOpen,
    fun _ => hCap1, by decide, fun _ _ _ => rfl⟩

#verify_inhabited
  Qsag.MigrationExecution.migration_unconditional_circuit_to_sacrifice_ceremony_bound
  Qsag.MigrationExecution.inhabited_unconditional_circuit_to_sacrifice_ceremony

#verify_constructive
  Qsag.MigrationExecution.exists_eval_nonzero_rustGf128
  Qsag.MigrationExecution.rustGf128_roots_le_of_coeffAt_nonzero
  Qsag.MigrationExecution.evalGates_lane_sound
  Qsag.MigrationExecution.false_witness_implies_pending_and_fault
  Qsag.MigrationExecution.packBlock128_getLsbD
  Qsag.MigrationExecution.superBlockDefect_ne_zero_of_gateErr
  Qsag.MigrationExecution.gammaCombinedDefect_bad_coins_le_one
  Qsag.MigrationExecution.round0IpClaim_err_eq_evalCoeffs
  Qsag.MigrationExecution.round0_false_gamma_survives_at_most_30_coins
  Qsag.MigrationExecution.tooth_round0_unlocked_mid_forges_every_coin
  Qsag.MigrationExecution.circuit_round0_discharges_hLink
  Qsag.MigrationExecution.round0Flush_false_gamma_accepting_coins_bound
  Qsag.MigrationExecution.d16_round0_sacrifice_bit_check_54_bound
  Qsag.MigrationExecution.migration_unconditional_circuit_to_sacrifice_ceremony_bound
  Qsag.MigrationExecution.outer_mpc_ceremony_constants_exact
  Qsag.MigrationExecution.rustBitCheckStages_sound
  Qsag.MigrationExecution.rust_bit_check_63_concrete_accepting_coins_bound
  Qsag.MigrationExecution.packBlock114_getLsbD
  Qsag.MigrationExecution.superBlock114Defect_ne_zero_of_gateErr
  Qsag.MigrationExecution.gamma114CombinedDefect_bad_coins_le_one
  Qsag.MigrationExecution.round0IpClaim19_err_eq_evalCoeffs
  Qsag.MigrationExecution.round0_d19_false_gamma_survives_at_most_36_coins
  Qsag.MigrationExecution.round0D19Flush_false_gamma_accepting_coins_bound
  Qsag.MigrationExecution.d19_round0_sacrifice_bit_check_63_bound
  Qsag.MigrationExecution.migration_d19_unconditional_circuit_to_sacrifice_ceremony_bound
  Qsag.MigrationExecution.fpRlc_false_triple_survives_at_most_one_coin
  Qsag.MigrationExecution.fpFoldRound_err
  Qsag.MigrationExecution.fpFoldRound_false_claim_survives_at_most_two_coins
  Qsag.MigrationExecution.fpBaseAccepts_false_claim_at_most_two_coins
  Qsag.MigrationExecution.fpFieldCheck_false_triple_accepting_coins_bound
  Qsag.MigrationExecution.fieldCheckBadCoinBound_closed_le
  Qsag.MigrationExecution.field_check_numerator_35_bound
  Qsag.MigrationExecution.tooth_field_check_numerator_34_too_small
  Qsag.MigrationExecution.migration_438_zkboo_and_ceremony_qrom_soundness
  Qsag.MigrationExecution.inhabited_unconditional_circuit_to_sacrifice_ceremony

/-! ### Executed teeth and witnesses of the sacrifice, flush and ceremony counts

Audited and paired in `Tests/MigrationTeeth`. They are proved here because they run `IpClaim.err`,
`sacrificeAccepts`, `flushBaseAccepts`, `ceremonyAccepts` and `stagedBadCoinBound`, whose bodies are
sealed outside this module. `rustGf128Mul` is sealed here too: each product below has an operand
`0#128` or `1#128` and is rewritten with `rustGf128Mul_one_left` and its three siblings. -/

set_option linter.unusedSimpArgs false

/-- Defect of the length-one claim `1 · 1 = c`. -/
private theorem unitClaim_err (c : RustGf128) :
    (⟨1, fun _ => 1#128, fun _ => 1#128, c⟩ : IpClaim).err = 1#128 ^^^ c := by
  simp only [IpClaim.err, rustDot, rustGf128Mul_one_left, BitVec.zero_xor]

/-- Commit order matters: for a false claim, every coin has a forging message
    when the message may be chosen after the coin. -/
theorem tooth_fold_message_after_coin_forges :
    ∃ s : IpClaim, s.err ≠ 0#128 ∧
      ∀ rk : RustGf128, ∃ m : FoldMessage, (foldRound s m rk).err = 0#128 := by
  refine ⟨⟨1, fun _ => 1#128, fun _ => 1#128, 0#128⟩, by rw [unitClaim_err]; decide, fun rk => ?_⟩
  exact ⟨_, fold_message_after_coin_cancels_defect _ rk⟩

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
    by rw [unitClaim_err]; decide, fun _ => rfl, ?_⟩
  simp only [sacrificeAccepts, baseAccepts, baseOpening, BaseOpening.check,
      rustGf128Mul_one_left, rustGf128Mul_one_right, rustGf128Mul_zero_left,
      rustGf128Mul_zero_right, BitVec.xor_self, BitVec.xor_zero, BitVec.zero_xor]
  decide

/-- A true two-element claim is accepted through one honest fold and the
    honest base case. -/
theorem inhabited_sacrifice_accepted :
    ∃ (p : FoldProver 1) (s : IpClaim) (coins : List RustGf128),
      SacrificeAccepted 1 p s coins := by
  refine ⟨(⟨0#128, 0#128⟩, fun _ => ⟨0#128, 0#128, 0#128, 0#128⟩),
    ⟨2, fun _ => 1#128, fun _ => 1#128, 0#128⟩, [1#128, 1#128], ?_⟩
  show sacrificeAccepts 1 _ _ _ = true
  simp only [sacrificeAccepts, foldRound, IpClaim.half, padded, baseAccepts, baseOpening,
      BaseOpening.check, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceLT, ↓reduceIte,
      rustGf128Mul_one_left, rustGf128Mul_one_right, rustGf128Mul_zero_left,
      rustGf128Mul_zero_right, BitVec.xor_self, BitVec.xor_zero, BitVec.zero_xor]
  decide

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
    by rw [unitClaim_err]; decide, by rw [unitClaim_err]; decide, ?_, ?_⟩
  · simp only [flushBaseAcceptsLaneZeroOnly, baseAccepts, baseOpening, BaseOpening.check,
      rustGf128Mul_one_left, rustGf128Mul_one_right, rustGf128Mul_zero_left,
      rustGf128Mul_zero_right, BitVec.xor_self, BitVec.xor_zero, BitVec.zero_xor]
    decide
  · simp only [flushBaseAccepts, baseAccepts, baseOpening, BaseOpening.check,
      rustGf128Mul_one_left, rustGf128Mul_one_right, rustGf128Mul_zero_left,
      rustGf128Mul_zero_right, BitVec.xor_self, BitVec.xor_zero, BitVec.zero_xor]
    decide

/-- The mutant ceremony gate that checks the flush of fork `0` only. -/
def ceremonyAcceptsForkZeroOnly (r : Nat) (p : CeremonyProver r) (cl : Fin 7 → FlushClaims)
    (coins : CeremonyCoins) : Bool :=
  flushAccepts r (p 0 coins) (cl 0) (coins 0)

/-- Checking one of the seven forks accepts a false repetition of another fork
    (repetition `64`, fork 1, lane 0); the seven-fork gate rejects it. -/
theorem tooth_ceremony_single_fork_check_accepts_false_repetition :
    ∃ (p : CeremonyProver 0) (cl : Fin 7 → FlushClaims) (rep : Fin 438) (coins : CeremonyCoins),
      FalseRepetition 0 p cl rep ∧
      ceremonyAcceptsForkZeroOnly 0 p cl coins = true ∧
      ceremonyAccepts 0 p cl coins = false := by
  refine ⟨fun _ _ => constFlushProver ⟨0#128, 0#128⟩ ⟨0#128, 0#128, 0#128, 0#128⟩ 0,
    fun b _ _ => ⟨1, fun _ => 1#128, fun _ => 1#128, if b.val = 0 then 1#128 else 0#128⟩,
    ⟨64, by decide⟩, fun _ => [(1#128, 1#128)],
    ⟨fun _ _ => rfl, by rw [unitClaim_err]; decide, by rw [unitClaim_err]; decide⟩, ?_, ?_⟩
  · simp only [ceremonyAcceptsForkZeroOnly, flushAccepts, flushBaseAccepts, constFlushProver,
      baseAccepts, baseOpening, BaseOpening.check,
      rustGf128Mul_one_left, rustGf128Mul_one_right, rustGf128Mul_zero_left,
      rustGf128Mul_zero_right, BitVec.xor_self, BitVec.xor_zero, BitVec.zero_xor]
    decide
  · simp only [ceremonyAccepts, flushAccepts, flushBaseAccepts, constFlushProver,
      baseAccepts, baseOpening, BaseOpening.check,
      rustGf128Mul_one_left, rustGf128Mul_one_right, rustGf128Mul_zero_left,
      rustGf128Mul_zero_right, BitVec.xor_self, BitVec.xor_zero, BitVec.zero_xor]
    decide

/-- The numerator `63` is not slack: `62 / (2^128 - 1)` is below the staged count. -/
theorem tooth_rust_bit_check_numerator_62_too_small :
    ¬ (stagedBadCoinBound (2 ^ 128) ((2 ^ 128) ^ rustBitCheckHalvingRounds * (2 ^ 128 - 1))
        (sacrificeBadCoinBound (2 ^ 128) (2 ^ 128 - 1) rustBitCheckHalvingRounds)
        rustBitCheckStageNumerators * (2 ^ 128 - 1) ≤
      62 * ((2 ^ 128) ^ rustBitCheckStageNumerators.length *
        ((2 ^ 128) ^ rustBitCheckHalvingRounds * (2 ^ 128 - 1)))) := by
  decide +kernel

/-- The `D0_BITS = 16` numerator `54` does not bound the Rust geometry. -/
theorem tooth_rust_bit_check_numerator_54_too_small :
    ¬ (stagedBadCoinBound (2 ^ 128) ((2 ^ 128) ^ rustBitCheckHalvingRounds * (2 ^ 128 - 1))
        (sacrificeBadCoinBound (2 ^ 128) (2 ^ 128 - 1) rustBitCheckHalvingRounds)
        rustBitCheckStageNumerators * (2 ^ 128 - 1) ≤
      54 * ((2 ^ 128) ^ rustBitCheckStageNumerators.length *
        ((2 ^ 128) ^ rustBitCheckHalvingRounds * (2 ^ 128 - 1)))) := by
  decide +kernel

/-- The hypotheses of `staged_sacrifice_false_claim_accepting_coins_bound` are jointly
    satisfiable: a stage that leaves the claim unchanged is sound with degree `0`. -/
theorem inhabited_staged_sacrifice_hypotheses :
    ∃ (S Sb : List RustGf128) (stage : Nat → IpClaim → Unit → RustGf128 → IpClaim)
      (ds : List Nat) (s : IpClaim),
      S.Nodup ∧ Sb.Nodup ∧
      StagesSound S stage (fun s => decide (s.err ≠ 0#128)) ds ∧ s.err ≠ 0#128 :=
  ⟨[0#128, 1#128], [1#128], fun _ s _ _ => s, [0], ⟨1, fun _ => 1#128, fun _ => 1#128, 0#128⟩,
    by decide, by decide,
    ⟨fun s _ hs => by
      have h : (fun _ : RustGf128 => !decide (s.err ≠ 0#128)) = fun _ => false :=
        funext (fun _ => by rw [show decide (s.err ≠ 0#128) = true from hs]; rfl)
      show (List.filter (fun _ => !decide (s.err ≠ 0#128)) [0#128, 1#128]).length ≤ 0
      rw [h]; decide, trivial⟩,
    by rw [unitClaim_err]; decide⟩

#verify_constructive
  Qsag.MigrationExecution.tooth_fold_message_after_coin_forges
  Qsag.MigrationExecution.tooth_sacrifice_without_product_test_accepts_false_claim
  Qsag.MigrationExecution.inhabited_sacrifice_accepted
  Qsag.MigrationExecution.tooth_flush_single_lane_check_accepts_false_lane
  Qsag.MigrationExecution.tooth_ceremony_single_fork_check_accepts_false_repetition
  Qsag.MigrationExecution.tooth_rust_bit_check_numerator_62_too_small
  Qsag.MigrationExecution.tooth_rust_bit_check_numerator_54_too_small
  Qsag.MigrationExecution.inhabited_staged_sacrifice_hypotheses
  Qsag.MigrationExecution.sacrifice_accepted_coins_have_round_count
#verify_inhabited Qsag.MigrationExecution.sacrifice_accepted_coins_have_round_count
  Qsag.MigrationExecution.inhabited_sacrifice_accepted

end MigrationExecution

end Qsag
end
