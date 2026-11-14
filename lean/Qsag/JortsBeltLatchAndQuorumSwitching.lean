module
/-
# Qsag.JortsBeltLatchAndQuorumSwitching — `Jorts` (Modes 3A & 3B), `BeltLatch`, `(t, n, f)` BFT Quorum-Switching, Committee-Partitioned Subtrees & Self-Verifying Pre-Stepped `GF(2^128)` Shamir `WOTS+C`

Self-contained constructive (`0 Classical.choice`) Lean 4.35 formalization of stateful threshold
hash-based signing (`Jorts` Modes 3A and 3B), durable `BeltLatch` consensus, `(t, n, f)` BFT
quorum-switching safety/necessity/availability, committee-partitioned `t`-of-`t` subtrees (`QS-A`)
vs global-tree quorum-independent allocation (`QS-B`), and self-verifying pre-stepped `(t, n)`
Shamir `WOTS+C` evaluation tables over `TowerElem 7` ($\mathbb{F}_{2^{128}}$) and 256-bit
`SHAKE256` digests:

1. **Constructive Finite Bitmask Calculus & Pigeonhole Witness Extraction (`CustodiansMask`)**:
   - `0 Classical.choice` decidable equality, inclusion-exclusion, difference bounds, and executable
     smallest-witness extraction (`extractMaskMember`, `extractBeltHonestQuorumWitness`,
     `chooseMasks`, `selectSubcommittee`).
2. **Exact Rust Domain Tags, Big-Endian Framing & `(t, n, f)` BFT `BeltLatch` Trilogy**:
   - Domain tags and big-endian codecs for `belt_latch.rs`; concrete wire operations below
     separate cSHAKE customization from the retained abstract certificate model
     (`"QSAG.BELT.LATCH.BINDING/v1"`, `"QSAG.BELT.ECHO.MAC/v1"`, `"QSAG.BELT.ECHO.KEY/v1"`,
     `"QSAG.BELT.LATCH.WAL.MAC/v1"`) and all 12 `quorum_jorts.rs` domain tags
     (`"QSAG.QUORUM.CHAIN/v1"` through `"QSAG.QUORUM.STAGE.PKSEED/v1"`), with proved injectivity
     and cross-domain non-collision (`encodeNatBeBytes_injective`, `encodeBeltLatchRecord_injective`,
     `quorumLeafRecordBinding_binding`, `allBeltAndQuorumDomainTags_nodup`).
   - **Sufficiency (`beltLatch_quorum_intersection_global_uniqueness`)**, **Necessity
     (`tooth_under_threshold_latch_quorum_switches_double_sign`)**, and **Availability
     (`beltLatch_safe_and_live_iff_n_ge_3f_plus_1`, `tooth_unbounded_epoch_jump_exhausts_tree`)**.
3. **Multi-Turn Committee-Partitioned `QS-A` vs Global-Tree `QS-B` (`QuorumJortsTurn`)**:
   - Multi-turn `List (QuorumJortsTurn n)` state machine tracking per-`(custodian, committee)`
     durable `BeltLatchNodeState` slots, monotone subtree leaf cursor progression across
     `chooseMasks n t`, `quorumEchoMacTag`-authenticated `QuorumCommitteeEcho` permits, global leaf
     non-equivocation (`committee_partitioned_jorts_safe_and_live_for_2f_plus_1`), and under-threshold
     split-view equivocation (`tooth_quorum_jorts_under_threshold_split_view_across_turns`).
   - Explicit `QS-A` vs `QS-B` anonymity boundary: `qs_a_leaf_index_identifies_committee` proves
     `QS-A` is *committee-revealing partitioned custody* (statistical distance `1` across distinct
     committees via `sig.leaf / leavesPerCommittee`, contrasted with `QS-B` global-tree
     quorum-independent leaf allocation), paired with `qs_a_single_signer_equiv_given_same_leaf_schedule`.
4. **Full `TowerElem 7` ($\mathbb{F}_{2^{128}}$) / 256-Bit 128-Chain `WOTS+C` Pre-Stepped Table**:
   - 2-limb `TowerElem 7` ($\mathbb{F}_{2^{128}}$) Shamir secret sharing of 256-bit `Digest256`
     chain states (`splitDigest256Tower128` / `joinTower128Digest256`) across `v = 128` base-4
     chains with `WOTS_TARGET_SUM = 192`, `(t - 1)`-collusion `SimpleEquiv` zero-knowledge for
     unopened prefixes, and MAC-free `SHAKE256` endpoint self-verification.
-/

public import Qsag.Digest256
public import Qsag.Constructive
public import Qsag.SimulationSpine
public import Qsag.Goldilocks
public import Qsag.BinaryTower
public import Qsag.UcGames
public import Qsag.BaggyAndRss256Security
public import Qsag.CustodySuiteFull
import all Qsag.UcGames
import all Qsag.BaggyAndRss256Security

import Qsag.Tactic.AssuranceKit

public section
namespace Qsag

set_option autoImplicit false

/-! ## §0. Constructive `0-Classical` Finite Bitmask Calculus & Pigeonhole Extractors -/

/-- Constructive bitmask subset of `Fin n` (`0 Classical.choice`). -/
structure CustodiansMask (n : Nat) where
  mem : Fin n → Bool

/-- Recursive head-prepending constructor on `CustodiansMask`. -/
def consMask (b : Bool) {n : Nat} (m : CustodiansMask n) : CustodiansMask (n + 1) where
  mem i :=
    match i with
    | ⟨0, _⟩ => b
    | ⟨k + 1, hk⟩ => m.mem ⟨k, Nat.lt_of_succ_lt_succ hk⟩

/-- Tail projection dropping index `0` from `CustodiansMask (n + 1)`. -/
def tailMask {n : Nat} (m : CustodiansMask (n + 1)) : CustodiansMask n where
  mem i := m.mem ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩

theorem consMask_head_tail {n : Nat} (m : CustodiansMask (n + 1)) :
    consMask (m.mem ⟨0, Nat.zero_lt_succ n⟩) (tailMask m) = m := by
  cases m with
  | mk f =>
    apply congrArg CustodiansMask.mk
    funext i
    cases i with
    | mk val isLt =>
      cases val <;> rfl

theorem consMask_inj {n : Nat} {b₁ b₂ : Bool} {m₁ m₂ : CustodiansMask n}
    (h : consMask b₁ m₁ = consMask b₂ m₂) : b₁ = b₂ ∧ m₁ = m₂ := by
  have hb : b₁ = b₂ := congrArg (fun x => x.mem ⟨0, Nat.zero_lt_succ n⟩) h
  have hm : m₁ = m₂ := by
    cases m₁ with
    | mk f₁ =>
      cases m₂ with
      | mk f₂ =>
        apply congrArg CustodiansMask.mk
        funext i
        exact congrArg (fun x => x.mem ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩) h
  exact ⟨hb, hm⟩

def maskEqDec : {n : Nat} → CustodiansMask n → CustodiansMask n → Bool
  | 0, _, _ => true
  | n + 1, a, b =>
    (a.mem ⟨0, Nat.zero_lt_succ n⟩ == b.mem ⟨0, Nat.zero_lt_succ n⟩) &&
      maskEqDec (tailMask a) (tailMask b)

theorem maskEqDec_iff_eq :
    ∀ {n : Nat} (a b : CustodiansMask n), maskEqDec a b = true ↔ a = b
  | 0, ⟨f⟩, ⟨g⟩ => by
    simp only [maskEqDec, true_iff]
    apply congrArg CustodiansMask.mk
    funext i
    exact Fin.elim0 i
  | n + 1, a, b => by
    simp only [maskEqDec, Bool.and_eq_true, beq_iff_eq, maskEqDec_iff_eq (tailMask a) (tailMask b)]
    constructor
    · rintro ⟨h0, hTail⟩
      rw [← consMask_head_tail a, ← consMask_head_tail b, h0, hTail]
    · rintro rfl
      exact ⟨rfl, rfl⟩

/-- Constructive `DecidableEq` on `CustodiansMask n` using zero `Classical.choice`. -/
instance constructiveCustodiansMaskDecidableEq (n : Nat) : DecidableEq (CustodiansMask n) :=
  fun a b =>
    if h : maskEqDec a b = true then
      .isTrue ((maskEqDec_iff_eq a b).mp h)
    else
      .isFalse (fun hEq => h ((maskEqDec_iff_eq a b).mpr hEq))

/-- Exact cardinality of a finite custodian bitmask. -/
@[expose] def maskCard : {n : Nat} → CustodiansMask n → Nat
  | 0, _ => 0
  | n + 1, S => (if S.mem ⟨0, Nat.zero_lt_succ n⟩ then 1 else 0) + maskCard (tailMask S)

/-- Intersection `A ∩ B` of two custodian bitmasks. -/
@[expose] def maskInter {n : Nat} (A B : CustodiansMask n) : CustodiansMask n where
  mem i := A.mem i && B.mem i

/-- Set difference `A \ B` of two custodian bitmasks. -/
@[expose] def maskDiff {n : Nat} (A B : CustodiansMask n) : CustodiansMask n where
  mem i := A.mem i && !B.mem i

/-- Subset predicate `A ⊆ B` on custodian bitmasks. -/
@[expose] def maskSub {n : Nat} (A B : CustodiansMask n) : Prop :=
  ∀ i : Fin n, A.mem i = true → B.mem i = true

def emptyMask (n : Nat) : CustodiansMask n := ⟨fun _ => false⟩

@[simp] theorem maskCard_zero (S : CustodiansMask 0) : maskCard S = 0 := rfl

@[simp] theorem maskCard_succ {n : Nat} (S : CustodiansMask (n + 1)) :
    maskCard S = (if S.mem ⟨0, Nat.zero_lt_succ n⟩ then 1 else 0) + maskCard (tailMask S) := rfl

@[simp] theorem tailMask_consMask {n : Nat} (b : Bool) (m : CustodiansMask n) :
    tailMask (consMask b m) = m := by
  cases m; rfl

@[simp] theorem maskCard_consMask {n : Nat} (b : Bool) (m : CustodiansMask n) :
    maskCard (consMask b m) = (if b then 1 else 0) + maskCard m := by
  simp only [maskCard_succ, tailMask_consMask]
  rfl

theorem maskCard_empty (n : Nat) : maskCard (emptyMask n) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [maskCard_succ, emptyMask, Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
    exact ih

theorem maskCard_le_n : ∀ {n : Nat} (S : CustodiansMask n), maskCard S ≤ n
  | 0, _ => Nat.le_refl 0
  | n + 1, S => by
    simp only [maskCard_succ]
    have ih := maskCard_le_n (tailMask S)
    cases S.mem ⟨0, Nat.zero_lt_succ n⟩ <;> simp <;> omega

theorem maskCard_mono : ∀ {n : Nat} {A B : CustodiansMask n},
    maskSub A B → maskCard A ≤ maskCard B
  | 0, _, _, _ => Nat.le_refl 0
  | n + 1, A, B, hSub => by
    simp only [maskCard_succ]
    have hTail : maskSub (tailMask A) (tailMask B) :=
      fun i hi => hSub ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ hi
    have ih := maskCard_mono hTail
    have h0 := hSub ⟨0, Nat.zero_lt_succ n⟩
    cases ha : A.mem ⟨0, Nat.zero_lt_succ n⟩
    · cases B.mem ⟨0, Nat.zero_lt_succ n⟩ <;> simp <;> omega
    · rw [h0 ha]
      simp only [↓reduceIte]
      omega

theorem maskCard_union_inter : ∀ {n : Nat} (A B : CustodiansMask n),
    maskCard ⟨fun i => A.mem i || B.mem i⟩ + maskCard (maskInter A B) =
      maskCard A + maskCard B
  | 0, _, _ => rfl
  | n + 1, A, B => by
    simp only [maskCard_succ]
    have ih := maskCard_union_inter (tailMask A) (tailMask B)
    have hU : tailMask ⟨fun i => A.mem i || B.mem i⟩ =
        ⟨fun i => (tailMask A).mem i || (tailMask B).mem i⟩ := rfl
    have hI : tailMask (maskInter A B) = maskInter (tailMask A) (tailMask B) := rfl
    have hInter0 : (maskInter A B).mem ⟨0, Nat.zero_lt_succ n⟩ =
        (A.mem ⟨0, Nat.zero_lt_succ n⟩ && B.mem ⟨0, Nat.zero_lt_succ n⟩) := rfl
    rw [hU, hI, hInter0]
    by_cases ha : A.mem ⟨0, Nat.zero_lt_succ n⟩ = true <;>
      by_cases hb : B.mem ⟨0, Nat.zero_lt_succ n⟩ = true
    · simp only [ha, hb, Bool.or_self, Bool.and_self, ↓reduceIte]; omega
    · have hbf : B.mem ⟨0, Nat.zero_lt_succ n⟩ = false := Bool.not_eq_true _ |>.mp hb
      simp only [ha, hbf, Bool.true_or, Bool.true_and, Bool.false_eq_true, ↓reduceIte]; omega
    · have haf : A.mem ⟨0, Nat.zero_lt_succ n⟩ = false := Bool.not_eq_true _ |>.mp ha
      simp only [haf, hb, Bool.false_or, Bool.false_and, Bool.false_eq_true, ↓reduceIte]; omega
    · have haf : A.mem ⟨0, Nat.zero_lt_succ n⟩ = false := Bool.not_eq_true _ |>.mp ha
      have hbf : B.mem ⟨0, Nat.zero_lt_succ n⟩ = false := Bool.not_eq_true _ |>.mp hb
      simp only [haf, hbf, Bool.or_self, Bool.and_self, Bool.false_eq_true, ↓reduceIte]; omega

/-- Constructive inclusion-exclusion lower bound: `|A| + |B| ≤ n + |A ∩ B|`. -/
theorem maskCard_inter_add_n_ge {n : Nat} (A B : CustodiansMask n) :
    maskCard A + maskCard B ≤ n + maskCard (maskInter A B) := by
  have hUI := maskCard_union_inter A B
  have hLe := maskCard_le_n ⟨fun i => A.mem i || B.mem i⟩
  omega

theorem maskCard_diff_add_inter : ∀ {n : Nat} (A B : CustodiansMask n),
    maskCard (maskDiff A B) + maskCard (maskInter A B) = maskCard A
  | 0, _, _ => rfl
  | n + 1, A, B => by
    simp only [maskCard_succ]
    have ih := maskCard_diff_add_inter (tailMask A) (tailMask B)
    have hD : tailMask (maskDiff A B) = maskDiff (tailMask A) (tailMask B) := rfl
    have hI : tailMask (maskInter A B) = maskInter (tailMask A) (tailMask B) := rfl
    have hDiff0 : (maskDiff A B).mem ⟨0, Nat.zero_lt_succ n⟩ =
        (A.mem ⟨0, Nat.zero_lt_succ n⟩ && !B.mem ⟨0, Nat.zero_lt_succ n⟩) := rfl
    have hInter0 : (maskInter A B).mem ⟨0, Nat.zero_lt_succ n⟩ =
        (A.mem ⟨0, Nat.zero_lt_succ n⟩ && B.mem ⟨0, Nat.zero_lt_succ n⟩) := rfl
    rw [hD, hI, hDiff0, hInter0]
    by_cases ha : A.mem ⟨0, Nat.zero_lt_succ n⟩ = true <;>
      by_cases hb : B.mem ⟨0, Nat.zero_lt_succ n⟩ = true
    · simp only [ha, hb, Bool.not_true, Bool.and_false, Bool.and_self, Bool.false_eq_true, ↓reduceIte]; omega
    · have hbf : B.mem ⟨0, Nat.zero_lt_succ n⟩ = false := Bool.not_eq_true _ |>.mp hb
      simp only [ha, hbf, Bool.not_false, Bool.and_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte]; omega
    · have haf : A.mem ⟨0, Nat.zero_lt_succ n⟩ = false := Bool.not_eq_true _ |>.mp ha
      simp only [haf, hb, Bool.false_and, Bool.false_eq_true, ↓reduceIte]; omega
    · have haf : A.mem ⟨0, Nat.zero_lt_succ n⟩ = false := Bool.not_eq_true _ |>.mp ha
      have hbf : B.mem ⟨0, Nat.zero_lt_succ n⟩ = false := Bool.not_eq_true _ |>.mp hb
      simp only [haf, hbf, Bool.false_and, Bool.false_eq_true, ↓reduceIte]; omega

theorem maskCard_diff_ge {n : Nat} (A B : CustodiansMask n) :
    maskCard A ≤ maskCard (maskDiff A B) + maskCard B := by
  have hSplit := maskCard_diff_add_inter A B
  have hSub : maskSub (maskInter A B) B := by
    intro i hi
    simp only [maskInter, Bool.and_eq_true] at hi
    exact hi.2
  have hMono := maskCard_mono hSub
  omega

theorem maskCard_singleton : ∀ {n : Nat} (target : Fin n),
    maskCard ⟨fun j => decide (j = target)⟩ = 1
  | 0, target => Fin.elim0 target
  | n + 1, ⟨0, _⟩ => by
    simp only [maskCard_succ, decide_true, ↓reduceIte]
    have hTailEmpty : tailMask ⟨fun j : Fin (n + 1) => decide (j = ⟨0, Nat.zero_lt_succ n⟩)⟩ =
        emptyMask n := by
      apply congrArg CustodiansMask.mk
      funext j
      dsimp only [tailMask, emptyMask]
      simp only [decide_eq_false_iff_not]
      intro hEq
      cases congrArg Fin.val hEq
    rw [hTailEmpty, maskCard_empty]
  | n + 1, ⟨k + 1, hk⟩ => by
    have h0Ne : (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1)) ≠ ⟨k + 1, hk⟩ :=
      fun hEq => by cases congrArg Fin.val hEq
    simp only [maskCard_succ, decide_eq_false h0Ne, Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
    have hTailShift :
        tailMask ⟨fun j : Fin (n + 1) => decide (j = ⟨k + 1, hk⟩)⟩ =
        ⟨fun j : Fin n => decide (j = ⟨k, Nat.lt_of_succ_lt_succ hk⟩)⟩ := by
      apply congrArg CustodiansMask.mk
      funext j
      dsimp only [tailMask]
      by_cases hjk : j.val = k
      · have h2 : j = ⟨k, Nat.lt_of_succ_lt_succ hk⟩ := Fin.ext hjk
        subst h2
        simp
      · have h1 : (⟨j.val + 1, Nat.succ_lt_succ j.2⟩ : Fin (n + 1)) ≠ ⟨k + 1, hk⟩ :=
          fun he => hjk (Nat.succ.inj (congrArg Fin.val he))
        have h2 : j ≠ ⟨k, Nat.lt_of_succ_lt_succ hk⟩ :=
          fun he => hjk (congrArg Fin.val he)
        simp [h1, h2]
    rw [hTailShift]
    exact maskCard_singleton ⟨k, Nat.lt_of_succ_lt_succ hk⟩

/-- Constructive executable witness extractor: given `0 < maskCard S`, computes the smallest-index
    custodian `p : Fin n` with `S.mem p = true` using **zero `Classical.choice`**. -/
def extractMaskMember : {n : Nat} → (S : CustodiansMask n) → 0 < maskCard S →
    { p : Fin n // S.mem p = true }
  | 0, _, hPos => False.elim (Nat.lt_irrefl 0 hPos)
  | n + 1, S, hPos =>
    if h0 : S.mem ⟨0, Nat.zero_lt_succ n⟩ = true then
      ⟨⟨0, Nat.zero_lt_succ n⟩, h0⟩
    else
      have h0f : S.mem ⟨0, Nat.zero_lt_succ n⟩ = false := Bool.eq_false_iff.mpr h0
      have hTailPos : 0 < maskCard (tailMask S) := by
        simp only [maskCard_succ, h0f, Bool.false_eq_true, ↓reduceIte, Nat.zero_add] at hPos
        exact hPos
      let ⟨pTail, hpTail⟩ := extractMaskMember (tailMask S) hTailPos
      ⟨⟨pTail.1 + 1, Nat.succ_lt_succ pTail.2⟩, hpTail⟩

/-- Constructive BFT Quorum-Intersection Honest Custodian Extractor (`0 Classical.choice`):
    Whenever `2 * q > n + f`, `|Q1| ≥ q`, `|Q2| ≥ q`, and `|Corrupt| ≤ f`, computes an explicit
    honest custodian `p : Fin n` in `(Q1 ∩ Q2) \ Corrupt`. -/
def extractBeltHonestQuorumWitness {n q f : Nat}
    (Q1 Q2 Corrupt : CustodiansMask n)
    (hQuorum : 2 * q > n + f)
    (hQ1 : q ≤ maskCard Q1)
    (hQ2 : q ≤ maskCard Q2)
    (hCorrupt : maskCard Corrupt ≤ f) :
    { p : Fin n // Q1.mem p = true ∧ Q2.mem p = true ∧ Corrupt.mem p = false } :=
  have hInterLb : f + 1 ≤ maskCard (maskInter Q1 Q2) := by
    have hIE := maskCard_inter_add_n_ge Q1 Q2
    omega
  have hHonestPos : 0 < maskCard (maskDiff (maskInter Q1 Q2) Corrupt) := by
    have hDiff := maskCard_diff_ge (maskInter Q1 Q2) Corrupt
    omega
  let ⟨p, hp⟩ := extractMaskMember (maskDiff (maskInter Q1 Q2) Corrupt) hHonestPos
  ⟨p, by
    simp only [maskDiff, maskInter, Bool.and_eq_true, Bool.not_eq_true'] at hp
    exact ⟨hp.1.1, hp.1.2, hp.2⟩⟩

/-! ## §1. Open-World Multi-Turn `(t, n, f)` `BeltLatch` & `Jorts` Modes 3A/3B Network -/

/-- Collision witness on a 256-bit hash function `H : List UInt8 → Digest256`. -/
structure HashCollision256 (H : List UInt8 → Digest256) where
  preA : List UInt8
  preB : List UInt8
  distinct : preA ≠ preB
  same_digest : H preA = H preB

/-- Encode `n` as `w` big-endian bytes (matching Rust `to_be_bytes()`). -/
def encodeNatBeBytes (w n : Nat) : List UInt8 :=
  be w n

/-- Decode a big-endian byte list into `Nat` (matching Rust `from_be_bytes`). -/
def decodeNatBeBytes (bytes : List UInt8) : Nat :=
  ofBE bytes

@[simp] theorem encodeNatBeBytes_length (w n : Nat) : (encodeNatBeBytes w n).length = w :=
  length_be w n

theorem decodeNatBeBytes_encodeNatBeBytes {w n : Nat} (hn : n < 256 ^ w) :
    decodeNatBeBytes (encodeNatBeBytes w n) = n :=
  ofBE_be hn

theorem encodeNatBeBytes_injective {w n m : Nat} (hn : n < 256 ^ w) (hm : m < 256 ^ w)
    (h : encodeNatBeBytes w n = encodeNatBeBytes w m) : n = m :=
  be_injective hn hm h

theorem encodeNatBeBytes_decodeNatBeBytes (xs : List UInt8) :
    encodeNatBeBytes xs.length (decodeNatBeBytes xs) = xs :=
  be_ofBE xs

private theorem pow2_256_eq_256_32 : (2 : Nat) ^ 256 = 256 ^ 32 := by
  change 2 ^ (8 * 32) = (2 ^ 8) ^ 32
  rw [Nat.pow_mul]

private theorem pow2_64_eq_256_8 : (2 : Nat) ^ 64 = 256 ^ 8 := by
  change 2 ^ (8 * 8) = (2 ^ 8) ^ 8
  rw [Nat.pow_mul]

private theorem pow2_32_eq_256_4 : (2 : Nat) ^ 32 = 256 ^ 4 := by
  change 2 ^ (8 * 4) = (2 ^ 8) ^ 4
  rw [Nat.pow_mul]

private theorem pow256_8_gt_64 : 64 < 256 ^ 8 := by
  calc 64 < 256 ^ 1 := by decide
    _ ≤ 256 ^ 8 := Nat.pow_le_pow_right (by decide) (by decide)

/-- **`#tooth` Endianness Sensitivity (`tooth_encodeNatBeBytes_ne_le`)**:
    8-byte big-endian encoding (`u64::to_be_bytes`) of `1` places `0x01` in the final byte
    (`[0, 0, 0, 0, 0, 0, 0, 1]`), strictly distinct from little-endian `[1, 0, 0, 0, 0, 0, 0, 0]`. -/
theorem tooth_encodeNatBeBytes_ne_le :
    encodeNatBeBytes 8 1 = [0, 0, 0, 0, 0, 0, 0, 1] ∧
    encodeNatBeBytes 8 1 ≠ [1, 0, 0, 0, 0, 0, 0, 0] := by
  decide

/-- Encode a 256-bit `Digest256` canonically as 32 big-endian bytes. -/
def encodeDigest256 (d : Digest256) : List UInt8 :=
  encodeNatBeBytes 32 d.toNat

/-- Decode the first 32 big-endian bytes into a 256-bit `Digest256`. -/
def digest256OfBytesBe (bytes : List UInt8) : Digest256 :=
  BitVec.ofNat 256 (decodeNatBeBytes (bytes.take 32))

theorem encodeDigest256_length (d : Digest256) : (encodeDigest256 d).length = 32 :=
  encodeNatBeBytes_length 32 d.toNat

theorem encodeDigest256_injective {a b : Digest256}
    (hEq : encodeDigest256 a = encodeDigest256 b) : a = b :=
  BitVec.eq_of_toNat_eq
    (encodeNatBeBytes_injective
      (Nat.lt_of_lt_of_eq a.isLt pow2_256_eq_256_32)
      (Nat.lt_of_lt_of_eq b.isLt pow2_256_eq_256_32) hEq)

theorem digest256OfBytesBe_encodeDigest256 (d : Digest256) :
    digest256OfBytesBe (encodeDigest256 d) = d := by
  unfold digest256OfBytesBe encodeDigest256
  rw [List.take_of_length_le (by rw [encodeNatBeBytes_length]; exact Nat.le_refl 32),
      decodeNatBeBytes_encodeNatBeBytes (Nat.lt_of_lt_of_eq d.isLt pow2_256_eq_256_32),
      BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- Concrete 24-round NIST FIPS 202 `SHAKE256` 256-bit digest (`Digest256`). -/
def shake256Digest256 (input : List UInt8) : Digest256 :=
  digest256OfBytesBe (shake256Xof 32 input)

/-- Concrete 24-round NIST SP 800-185 `cSHAKE256` 256-bit digest (`Digest256`). -/
def cshake256Digest256 (customization input : List UInt8) : Digest256 :=
  digest256OfBytesBe (cshake256Bytes customization input)

/-- Durable `BeltLatch` epoch binding record (`epoch`, `msgDigest`, `retrySalt`, `targetSumDigits`). -/
structure BeltLatchRecord where
  epoch : UInt64
  msgDigest : Digest256
  retrySalt : Digest256
  targetSumDigits : List UInt8
  deriving DecidableEq, Repr

/-! ### Exact `belt_latch.rs` & `quorum_jorts.rs` Domain Separators (`ByteArray` Parity) -/

/-- Exact 26-byte domain tag `"QSAG.BELT.LATCH.BINDING/v1"` (`belt_latch.rs:84`). -/
def beltLatchBindingTag : ByteArray :=
  ByteArray.mk #[0x51, 0x53, 0x41, 0x47, 0x2E, 0x42, 0x45, 0x4C, 0x54, 0x2E, 0x4C, 0x41, 0x54,
                 0x43, 0x48, 0x2E, 0x42, 0x49, 0x4E, 0x44, 0x49, 0x4E, 0x47, 0x2F, 0x76, 0x31]

theorem beltLatchBindingTag_size : beltLatchBindingTag.size = 26 := by
  simp [beltLatchBindingTag, ByteArray.size]

/-- Exact 21-byte domain tag `"QSAG.BELT.ECHO.MAC/v1"` (`belt_latch.rs:66`). -/
def beltEchoMacTag : ByteArray :=
  ByteArray.mk #[0x51, 0x53, 0x41, 0x47, 0x2E, 0x42, 0x45, 0x4C, 0x54, 0x2E, 0x45, 0x43, 0x48,
                 0x4F, 0x2E, 0x4D, 0x41, 0x43, 0x2F, 0x76, 0x31]

theorem beltEchoMacTag_size : beltEchoMacTag.size = 21 := by
  simp [beltEchoMacTag, ByteArray.size]

/-- Exact 21-byte domain tag `"QSAG.BELT.ECHO.KEY/v1"` (`belt_latch.rs:65`). -/
def beltEchoKeyTag : ByteArray :=
  ByteArray.mk #[0x51, 0x53, 0x41, 0x47, 0x2E, 0x42, 0x45, 0x4C, 0x54, 0x2E, 0x45, 0x43, 0x48,
                 0x4F, 0x2E, 0x4B, 0x45, 0x59, 0x2F, 0x76, 0x31]

theorem beltEchoKeyTag_size : beltEchoKeyTag.size = 21 := by
  simp [beltEchoKeyTag, ByteArray.size]

/-- Exact 26-byte domain tag `"QSAG.BELT.LATCH.WAL.MAC/v1"` (`belt_latch.rs:68`). -/
def beltLatchWalMacTag : ByteArray :=
  ByteArray.mk #[0x51, 0x53, 0x41, 0x47, 0x2E, 0x42, 0x45, 0x4C, 0x54, 0x2E, 0x4C, 0x41, 0x54,
                 0x43, 0x48, 0x2E, 0x57, 0x41, 0x4C, 0x2E, 0x4D, 0x41, 0x43, 0x2F, 0x76, 0x31]

theorem beltLatchWalMacTag_size : beltLatchWalMacTag.size = 26 := by
  simp [beltLatchWalMacTag, ByteArray.size]

/-- Exact 20-byte domain tag `"QSAG.QUORUM.CHAIN/v1"` (`quorum_jorts.rs:73`). -/
def quorumChainTag : ByteArray :=
  ByteArray.mk #[0x51, 0x53, 0x41, 0x47, 0x2E, 0x51, 0x55, 0x4F, 0x52, 0x55, 0x4D, 0x2E, 0x43,
                 0x48, 0x41, 0x49, 0x4E, 0x2F, 0x76, 0x31]

theorem quorumChainTag_size : quorumChainTag.size = 20 := by
  simp [quorumChainTag, ByteArray.size]

/-- Exact 19-byte domain tag `"QSAG.QUORUM.LEAF/v1"` (`quorum_jorts.rs:74`). -/
def quorumLeafTag : ByteArray :=
  ByteArray.mk #[0x51, 0x53, 0x41, 0x47, 0x2E, 0x51, 0x55, 0x4F, 0x52, 0x55, 0x4D, 0x2E, 0x4C,
                 0x45, 0x41, 0x46, 0x2F, 0x76, 0x31]

theorem quorumLeafTag_size : quorumLeafTag.size = 19 := by
  simp [quorumLeafTag, ByteArray.size]

/-- Exact 30-byte domain tag `"QSAG.QUORUM.LEAF.UNASSIGNED/v1"` (`quorum_jorts.rs:75`). -/
def quorumLeafUnassignedTag : ByteArray :=
  ByteArray.mk #[0x51, 0x53, 0x41, 0x47, 0x2E, 0x51, 0x55, 0x4F, 0x52, 0x55, 0x4D, 0x2E, 0x4C,
                 0x45, 0x41, 0x46, 0x2E, 0x55, 0x4E, 0x41, 0x53, 0x53, 0x49, 0x47, 0x4E, 0x45,
                 0x44, 0x2F, 0x76, 0x31]

theorem quorumLeafUnassignedTag_size : quorumLeafUnassignedTag.size = 30 := by
  simp [quorumLeafUnassignedTag, ByteArray.size]

/-- Exact 19-byte domain tag `"QSAG.QUORUM.NODE/v1"` (`quorum_jorts.rs:76`). -/
def quorumNodeTag : ByteArray :=
  ByteArray.mk #[0x51, 0x53, 0x41, 0x47, 0x2E, 0x51, 0x55, 0x4F, 0x52, 0x55, 0x4D, 0x2E, 0x4E,
                 0x4F, 0x44, 0x45, 0x2F, 0x76, 0x31]

theorem quorumNodeTag_size : quorumNodeTag.size = 19 := by
  simp [quorumNodeTag, ByteArray.size]

/-- Exact 18-byte domain tag `"QSAG.QUORUM.MSG/v1"` (`quorum_jorts.rs:77`). -/
def quorumMsgTag : ByteArray :=
  ByteArray.mk #[0x51, 0x53, 0x41, 0x47, 0x2E, 0x51, 0x55, 0x4F, 0x52, 0x55, 0x4D, 0x2E, 0x4D,
                 0x53, 0x47, 0x2F, 0x76, 0x31]

theorem quorumMsgTag_size : quorumMsgTag.size = 18 := by
  simp [quorumMsgTag, ByteArray.size]

/-- Exact 21-byte domain tag `"QSAG.QUORUM.DIGEST/v1"` (`quorum_jorts.rs:78`). -/
def quorumDigestTag : ByteArray :=
  ByteArray.mk #[0x51, 0x53, 0x41, 0x47, 0x2E, 0x51, 0x55, 0x4F, 0x52, 0x55, 0x4D, 0x2E, 0x44,
                 0x49, 0x47, 0x45, 0x53, 0x54, 0x2F, 0x76, 0x31]

theorem quorumDigestTag_size : quorumDigestTag.size = 21 := by
  simp [quorumDigestTag, ByteArray.size]

/-- Exact 22-byte domain tag `"QSAG.QUORUM.BINDING/v1"` (`quorum_jorts.rs:79`). -/
def quorumBindingTag : ByteArray :=
  ByteArray.mk #[0x51, 0x53, 0x41, 0x47, 0x2E, 0x51, 0x55, 0x4F, 0x52, 0x55, 0x4D, 0x2E, 0x42,
                 0x49, 0x4E, 0x44, 0x49, 0x4E, 0x47, 0x2F, 0x76, 0x31]

theorem quorumBindingTag_size : quorumBindingTag.size = 22 := by
  simp [quorumBindingTag, ByteArray.size]

/-- Exact 23-byte domain tag `"QSAG.QUORUM.ECHO.MAC/v1"` (`quorum_jorts.rs:80`). -/
def quorumEchoMacTag : ByteArray :=
  ByteArray.mk #[0x51, 0x53, 0x41, 0x47, 0x2E, 0x51, 0x55, 0x4F, 0x52, 0x55, 0x4D, 0x2E, 0x45,
                 0x43, 0x48, 0x4F, 0x2E, 0x4D, 0x41, 0x43, 0x2F, 0x76, 0x31]

theorem quorumEchoMacTag_size : quorumEchoMacTag.size = 23 := by
  simp [quorumEchoMacTag, ByteArray.size]

/-- Exact 22-byte domain tag `"QSAG.QUORUM.ACK.MAC/v1"` (`quorum_jorts.rs:81`). -/
def quorumAckMacTag : ByteArray :=
  ByteArray.mk #[0x51, 0x53, 0x41, 0x47, 0x2E, 0x51, 0x55, 0x4F, 0x52, 0x55, 0x4D, 0x2E, 0x41,
                 0x43, 0x4B, 0x2E, 0x4D, 0x41, 0x43, 0x2F, 0x76, 0x31]

theorem quorumAckMacTag_size : quorumAckMacTag.size = 22 := by
  simp [quorumAckMacTag, ByteArray.size]

/-- Exact 23-byte domain tag `"QSAG.QUORUM.PAIR.KEY/v1"` (`quorum_jorts.rs:82`). -/
def quorumPairKeyTag : ByteArray :=
  ByteArray.mk #[0x51, 0x53, 0x41, 0x47, 0x2E, 0x51, 0x55, 0x4F, 0x52, 0x55, 0x4D, 0x2E, 0x50,
                 0x41, 0x49, 0x52, 0x2E, 0x4B, 0x45, 0x59, 0x2F, 0x76, 0x31]

theorem quorumPairKeyTag_size : quorumPairKeyTag.size = 23 := by
  simp [quorumPairKeyTag, ByteArray.size]

/-- Exact 23-byte domain tag `"QSAG.QUORUM.STAGE.SK/v1"` (`quorum_jorts.rs:83`). -/
def quorumStageSkTag : ByteArray :=
  ByteArray.mk #[0x51, 0x53, 0x41, 0x47, 0x2E, 0x51, 0x55, 0x4F, 0x52, 0x55, 0x4D, 0x2E, 0x53,
                 0x54, 0x41, 0x47, 0x45, 0x2E, 0x53, 0x4B, 0x2F, 0x76, 0x31]

theorem quorumStageSkTag_size : quorumStageSkTag.size = 23 := by
  simp [quorumStageSkTag, ByteArray.size]

/-- Exact 27-byte domain tag `"QSAG.QUORUM.STAGE.PKSEED/v1"` (`quorum_jorts.rs:84`). -/
def quorumStagePkSeedTag : ByteArray :=
  ByteArray.mk #[0x51, 0x53, 0x41, 0x47, 0x2E, 0x51, 0x55, 0x4F, 0x52, 0x55, 0x4D, 0x2E, 0x53,
                 0x54, 0x41, 0x47, 0x45, 0x2E, 0x50, 0x4B, 0x53, 0x45, 0x45, 0x44, 0x2F, 0x76, 0x31]

theorem quorumStagePkSeedTag_size : quorumStagePkSeedTag.size = 27 := by
  simp [quorumStagePkSeedTag, ByteArray.size]

/-- Complete roster of all 16 `BeltLatch` and `QuorumJorts` domain separator byte lists. -/
def allBeltAndQuorumDomainTags : List (List UInt8) :=
  [ beltLatchBindingTag.data.toList,
    beltEchoMacTag.data.toList,
    beltEchoKeyTag.data.toList,
    beltLatchWalMacTag.data.toList,
    quorumChainTag.data.toList,
    quorumLeafTag.data.toList,
    quorumLeafUnassignedTag.data.toList,
    quorumNodeTag.data.toList,
    quorumMsgTag.data.toList,
    quorumDigestTag.data.toList,
    quorumBindingTag.data.toList,
    quorumEchoMacTag.data.toList,
    quorumAckMacTag.data.toList,
    quorumPairKeyTag.data.toList,
    quorumStageSkTag.data.toList,
    quorumStagePkSeedTag.data.toList ]

/-- Pairwise distinctness of all 16 `belt_latch.rs` and `quorum_jorts.rs` domain tags. -/
theorem allBeltAndQuorumDomainTags_nodup :
    allBeltAndQuorumDomainTags.length = 16 ∧ allBeltAndQuorumDomainTags.Nodup := by
  decide

/-! ### Big-Endian `BeltLatchRecord` Encoding & Commitment Binding (`belt_latch.rs:82-92`) -/

/-- Self-delimiting LEB128 multi-frame encoding of `BeltLatchRecord` with 8-byte big-endian `epoch`
    (`self.epoch.to_be_bytes()`, matching `BeltLatchRecord::binding` in `belt_latch.rs:85-90`). -/
def encodeBeltLatchRecord (rec : BeltLatchRecord) : List UInt8 :=
  encodeMultiFrame
    [ encodeNatBeBytes 8 rec.epoch.toNat,
      encodeDigest256 rec.msgDigest,
      encodeDigest256 rec.retrySalt,
      rec.targetSumDigits ]

private theorem list4_eq_iff {α : Type} {a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : α}
    (h : [a₁, b₁, c₁, d₁] = [a₂, b₂, c₂, d₂]) :
    a₁ = a₂ ∧ b₁ = b₂ ∧ c₁ = c₂ ∧ d₁ = d₂ := by
  have h1 := List.cons.inj h
  have h2 := List.cons.inj h1.2
  have h3 := List.cons.inj h2.2
  have h4 := List.cons.inj h3.2
  exact ⟨h1.1, h2.1, h3.1, h4.1⟩

/-- Unconditional constructive injectivity of `encodeBeltLatchRecord` (`0 Classical.choice`). -/
theorem encodeBeltLatchRecord_injective {r₁ r₂ : BeltLatchRecord}
    (hEq : encodeBeltLatchRecord r₁ = encodeBeltLatchRecord r₂) : r₁ = r₂ := by
  obtain ⟨hEp, hMd, hSalt, hDig⟩ := list4_eq_iff (encodeMultiFrame_injective hEq)
  have hEpNat : r₁.epoch.toNat = r₂.epoch.toNat :=
    encodeNatBeBytes_injective
      (Nat.lt_of_lt_of_eq r₁.epoch.toBitVec.isLt pow2_64_eq_256_8)
      (Nat.lt_of_lt_of_eq r₂.epoch.toBitVec.isLt pow2_64_eq_256_8) hEp
  have hEpEq : r₁.epoch = r₂.epoch :=
    UInt64.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq hEpNat)
  have hMdEq := encodeDigest256_injective hMd
  have hSaltEq := encodeDigest256_injective hSalt
  cases r₁; cases r₂
  dsimp only at hEpEq hMdEq hSaltEq hDig
  subst hEpEq hMdEq hSaltEq hDig
  rfl

/-- Abstract certificate-model commitment (not the Rust cSHAKE specialization) under `"QSAG.BELT.LATCH.BINDING/v1"`. -/
def beltRecordBinding (H : List UInt8 → Digest256) (rec : BeltLatchRecord) : Digest256 :=
  H (encodeMultiFrame [beltLatchBindingTag.data.toList, encodeBeltLatchRecord rec])

/-- Concrete `cSHAKE256` specialization matching `BeltLatchRecord::binding` (`belt_latch.rs:82-92`). -/
def beltRecordBindingCshake256 (rec : BeltLatchRecord) : Digest256 :=
  cshake256Digest256 beltLatchBindingTag.data.toList (encodeBeltLatchRecord rec)

/-- Constructive commitment binding (`0 Classical.choice`): equal bindings imply identical
    `BeltLatchRecord`s or an explicit `HashCollision256 H`. -/
theorem beltRecordBinding_binding (H : List UInt8 → Digest256)
    {r₁ r₂ : BeltLatchRecord}
    (hBind : beltRecordBinding H r₁ = beltRecordBinding H r₂) :
    r₁ = r₂ ∨ Nonempty (HashCollision256 H) := by
  let pre₁ := encodeMultiFrame [beltLatchBindingTag.data.toList, encodeBeltLatchRecord r₁]
  let pre₂ := encodeMultiFrame [beltLatchBindingTag.data.toList, encodeBeltLatchRecord r₂]
  if hPre : pre₁ = pre₂ then
    have hL := encodeMultiFrame_injective hPre
    injection hL with _ hRest
    injection hRest with hPay _
    exact .inl (encodeBeltLatchRecord_injective hPay)
  else
    exact .inr ⟨⟨pre₁, pre₂, hPre, hBind⟩⟩

/-- Legacy abstract pair-key derivation; use `deriveBeltEchoMacKeyCshake256` for Rust. Domain: `"QSAG.BELT.ECHO.KEY/v1"` (`belt_latch.rs:449-470`). -/
def deriveBeltEchoMacKey
    (H : List UInt8 → Digest256)
    (context : List UInt8) (a b : Nat) (pairSecrets : List (List UInt8)) : Digest256 :=
  let lo := min a b
  let hi := max a b
  H (encodeMultiFrame
      (beltEchoKeyTag.data.toList :: context :: encodeNatBeBytes 8 lo :: encodeNatBeBytes 8 hi :: pairSecrets))

theorem deriveBeltEchoMacKey_symm
    (H : List UInt8 → Digest256)
    (context : List UInt8) (a b : Nat) (pairSecrets : List (List UInt8)) :
    deriveBeltEchoMacKey H context a b pairSecrets =
      deriveBeltEchoMacKey H context b a pairSecrets := by
  unfold deriveBeltEchoMacKey
  rw [Nat.min_comm, Nat.max_comm]

/-- Durable WAL seal tag under `"QSAG.BELT.LATCH.WAL.MAC/v1"` (`FsBeltWal::tag`, `belt_latch.rs:271-273`). -/
def computeBeltWalSealTag
    (H : List UInt8 → Digest256) (walKey : Digest256) (body : List UInt8) : Digest256 :=
  H (encodeMultiFrame [beltLatchWalMacTag.data.toList, encodeMultiFrame [encodeDigest256 walKey, body]])

theorem computeBeltWalSealTag_binding (H : List UInt8 → Digest256)
    {k₁ k₂ : Digest256} {b₁ b₂ : List UInt8}
    (hTag : computeBeltWalSealTag H k₁ b₁ = computeBeltWalSealTag H k₂ b₂) :
    (k₁ = k₂ ∧ b₁ = b₂) ∨ Nonempty (HashCollision256 H) := by
  let pre₁ := encodeMultiFrame [beltLatchWalMacTag.data.toList, encodeMultiFrame [encodeDigest256 k₁, b₁]]
  let pre₂ := encodeMultiFrame [beltLatchWalMacTag.data.toList, encodeMultiFrame [encodeDigest256 k₂, b₂]]
  if hPre : pre₁ = pre₂ then
    have hOuter := encodeMultiFrame_injective hPre
    injection hOuter with _ hR1
    injection hR1 with hInnerEq _
    have hInner := encodeMultiFrame_injective hInnerEq
    injection hInner with hKey hR2
    injection hR2 with hBody _
    exact .inl ⟨encodeDigest256_injective hKey, hBody⟩
  else
    exact .inr ⟨⟨pre₁, pre₂, hPre, hTag⟩⟩

/-- Pairwise MAC-authenticated `BeltEcho` message from `sender` to `receiver`. -/
structure AuthenticatedBeltEcho (n : Nat) where
  sender : Fin n
  receiver : Fin n
  record : BeltLatchRecord
  binding : Digest256
  macTag : Digest256
  deriving DecidableEq, Repr

/-- Legacy abstract certificate MAC over `"QSAG.BELT.ECHO.MAC/v1"` and big-endian `(sender, receiver, record)`
    (`belt_latch.rs:527-547`). -/
def computeBeltEchoMac {n : Nat}
    (MAC : Digest256 → List UInt8 → Digest256)
    (pairwiseKey : Digest256) (sender receiver : Fin n) (rec : BeltLatchRecord) : Digest256 :=
  MAC pairwiseKey
    (encodeMultiFrame
      [ beltEchoMacTag.data.toList,
        encodeNatBeBytes 8 sender.val,
        encodeNatBeBytes 8 receiver.val,
        encodeBeltLatchRecord rec ])

/-- Verify an `AuthenticatedBeltEcho` under `H` and pairwise symmetric key `pairwiseKey`. -/
def verifyAuthenticatedBeltEcho {n : Nat}
    (H : List UInt8 → Digest256)
    (MAC : Digest256 → List UInt8 → Digest256)
    (pairwiseKey : Digest256) (expectedSender expectedReceiver : Fin n)
    (expectedRec : BeltLatchRecord) (echo : AuthenticatedBeltEcho n) : Bool :=
  decide (echo.sender = expectedSender) &&
  decide (echo.receiver = expectedReceiver) &&
  decide (echo.record = expectedRec) &&
  decide (echo.binding = beltRecordBinding H expectedRec) &&
  decide (echo.macTag = computeBeltEchoMac MAC pairwiseKey expectedSender expectedReceiver expectedRec)

/-! ### Exact `quorum_jorts.rs` / `hash.rs` 8-Byte Big-Endian Framing & Cryptographic Primitives -/

/-- 8-byte big-endian length-framed byte slice `(x.len() as u64).to_be_bytes() || x` (`hash.rs:10-11`). -/
def quorumFrameField (x : List UInt8) : List UInt8 :=
  encodeNatBeBytes 8 x.length ++ x

/-- Concatenate 8-byte big-endian length-framed slices (`hash.rs:15-18`). -/
def quorumFrameFields : List (List UInt8) → List UInt8
  | [] => []
  | x :: xs => quorumFrameField x ++ quorumFrameFields xs

/-- Canonical `hash.rs` domain-and-parts framing `absorb_framed(domain, parts)`. -/
def quorumEncodeFramed (domain : ByteArray) (parts : List (List UInt8)) : List UInt8 :=
  quorumFrameField domain.data.toList ++ quorumFrameFields parts

theorem quorumFrameField_prefix_inj {x y r₁ r₂ : List UInt8}
    (hx : x.length < 256 ^ 8) (hy : y.length < 256 ^ 8)
    (h : quorumFrameField x ++ r₁ = quorumFrameField y ++ r₂) :
    x = y ∧ r₁ = r₂ := by
  simp only [quorumFrameField, List.append_assoc] at h
  have hLen8 : (encodeNatBeBytes 8 x.length).length = (encodeNatBeBytes 8 y.length).length := by
    rw [encodeNatBeBytes_length, encodeNatBeBytes_length]
  obtain ⟨hBe, hTail⟩ := List.append_inj h hLen8
  have hLenEq : x.length = y.length := encodeNatBeBytes_injective hx hy hBe
  exact List.append_inj hTail hLenEq

theorem quorumEncodeFramed_cross_domain_ne
    {d₁ d₂ : ByteArray} (p₁ p₂ : List (List UInt8))
    (hd₁ : d₁.data.toList.length < 256 ^ 8) (hd₂ : d₂.data.toList.length < 256 ^ 8)
    (hNe : d₁.data.toList ≠ d₂.data.toList) :
    quorumEncodeFramed d₁ p₁ ≠ quorumEncodeFramed d₂ p₂ :=
  fun hEq => hNe (quorumFrameField_prefix_inj hd₁ hd₂ hEq).1

private theorem quorumFrameFields_inj_of_len :
    ∀ {xs ys : List (List UInt8)},
      xs.length = ys.length →
      (∀ x ∈ xs, x.length < 256 ^ 8) →
      (∀ y ∈ ys, y.length < 256 ^ 8) →
      quorumFrameFields xs = quorumFrameFields ys →
      xs = ys
  | [], [], _, _, _, _ => rfl
  | x :: xs, y :: ys, hLen, hBx, hBy, hEq => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hLen
    simp only [quorumFrameFields] at hEq
    obtain ⟨hxEq, hRest⟩ :=
      quorumFrameField_prefix_inj (hBx x (.head xs)) (hBy y (.head ys)) hEq
    have hTail :=
      quorumFrameFields_inj_of_len hLen
        (fun z hz => hBx z (.tail x hz))
        (fun z hz => hBy z (.tail y hz)) hRest
    subst hxEq hTail; rfl

theorem quorumEncodeFramed_same_arity_injective
    (domain : ByteArray) (hd : domain.data.toList.length < 256 ^ 8)
    {xs ys : List (List UInt8)}
    (hLen : xs.length = ys.length)
    (hBx : ∀ x ∈ xs, x.length < 256 ^ 8)
    (hBy : ∀ y ∈ ys, y.length < 256 ^ 8)
    (hEq : quorumEncodeFramed domain xs = quorumEncodeFramed domain ys) :
    xs = ys := by
  obtain ⟨_, hRest⟩ := quorumFrameField_prefix_inj hd hd hEq
  exact quorumFrameFields_inj_of_len hLen hBx hBy hRest

/-- Public key of `quorum_jorts.rs:181-186` (`QuorumPublicKey`). -/
structure QuorumPublicKey where
  pkSeed : Digest256
  root : Digest256
  height : UInt8
  deriving DecidableEq, Repr

/-- Signature of `quorum_jorts.rs:189-195` (`QuorumJortsSig`). -/
structure QuorumJortsSig where
  leaf : UInt64
  counter : UInt32
  nodes : List Digest256
  authPath : List Digest256
  deriving DecidableEq, Repr

/-- Leaf binding record of `quorum_jorts.rs:311-317` (`LeafRecord`). -/
structure QuorumLeafRecord where
  leaf : UInt64
  msgHash : Digest256
  counter : UInt32
  digits : List UInt8
  deriving DecidableEq, Repr

/-- Derive public chain seed under `"QSAG.QUORUM.STAGE.PKSEED/v1"` (`quorum_jorts.rs:713, 1266`). -/
def quorumStagePkSeed (H : List UInt8 → Digest256) (seed : Digest256) : Digest256 :=
  H (quorumEncodeFramed quorumStagePkSeedTag [encodeDigest256 seed])

/-- Derive chain secret start under `"QSAG.QUORUM.STAGE.SK/v1"` (`quorum_jorts.rs:566-569`). -/
def quorumStageChainSk (H : List UInt8 → Digest256)
    (seed : Digest256) (leaf : UInt64) (chain : UInt32) : Digest256 :=
  H (quorumEncodeFramed quorumStageSkTag
      [encodeDigest256 seed, encodeNatBeBytes 8 leaf.toNat, encodeNatBeBytes 4 chain.toNat])

/-- Derive symmetric pairwise MAC key under `"QSAG.QUORUM.PAIR.KEY/v1"` (`quorum_jorts.rs:548-558`). -/
def quorumDerivePairKey (H : List UInt8 → Digest256)
    (seed : Digest256) (i j : Nat) : Digest256 :=
  let lo := min i j
  let hi := max i j
  H (quorumEncodeFramed quorumPairKeyTag
      [encodeDigest256 seed, encodeNatBeBytes 8 lo, encodeNatBeBytes 8 hi])

theorem quorumDerivePairKey_symm (H : List UInt8 → Digest256)
    (seed : Digest256) (i j : Nat) :
    quorumDerivePairKey H seed i j = quorumDerivePairKey H seed j i := by
  unfold quorumDerivePairKey
  rw [Nat.min_comm, Nat.max_comm]

/-- One step of a Quorum `WOTS+C` chain under `"QSAG.QUORUM.CHAIN/v1"` (`quorum_jorts.rs:205-211`). -/
def quorumChainStep (H : List UInt8 → Digest256)
    (pkSeed : Digest256) (leaf : UInt64) (chain step : Nat) (input : Digest256) : Digest256 :=
  let adrs := encodeNatBeBytes 8 leaf.toNat ++ encodeNatBeBytes 4 chain ++ encodeNatBeBytes 4 step
  H (quorumEncodeFramed quorumChainTag [encodeDigest256 pkSeed, adrs, encodeDigest256 input])

/-- Assigned leaf hash over public chain ends under `"QSAG.QUORUM.LEAF/v1"` (`quorum_jorts.rs:230-235`). -/
def quorumLeafHash (H : List UInt8 → Digest256)
    (pkSeed : Digest256) (leaf : UInt64) (ends : List Digest256) : Digest256 :=
  H (quorumEncodeFramed quorumLeafTag
      [encodeDigest256 pkSeed, encodeNatBeBytes 8 leaf.toNat, ends.flatMap encodeDigest256])

/-- Unassigned leaf sentinel hash under `"QSAG.QUORUM.LEAF.UNASSIGNED/v1"` (`quorum_jorts.rs:239-241`). -/
def quorumUnassignedLeafHash (H : List UInt8 → Digest256)
    (pkSeed : Digest256) (leaf : UInt64) : Digest256 :=
  H (quorumEncodeFramed quorumLeafUnassignedTag
      [encodeDigest256 pkSeed, encodeNatBeBytes 8 leaf.toNat])

/-- Internal Merkle node hash under `"QSAG.QUORUM.NODE/v1"` (`quorum_jorts.rs:243-248`). -/
def quorumMerkleNodeHash (H : List UInt8 → Digest256)
    (pkSeed : Digest256) (level : UInt8) (index : UInt64) (left right : Digest256) : Digest256 :=
  H (quorumEncodeFramed quorumNodeTag
      [encodeDigest256 pkSeed, [level], encodeNatBeBytes 8 index.toNat,
       encodeDigest256 left, encodeDigest256 right])

/-- Cross-domain Merkle tree separation: assigned leaves, unassigned leaves, and internal nodes
    never collide unless `H` suffers an explicit `HashCollision256 H`. -/
theorem quorumTreeDomainSeparation (H : List UInt8 → Digest256)
    (pk₁ pk₂ pk₃ : Digest256) (l₁ l₂ idx : UInt64) (ends : List Digest256)
    (lvl : UInt8) (left right : Digest256) :
    (quorumLeafHash H pk₁ l₁ ends = quorumUnassignedLeafHash H pk₂ l₂ →
      Nonempty (HashCollision256 H)) ∧
    (quorumLeafHash H pk₁ l₁ ends = quorumMerkleNodeHash H pk₃ lvl idx left right →
      Nonempty (HashCollision256 H)) ∧
    (quorumUnassignedLeafHash H pk₂ l₂ = quorumMerkleNodeHash H pk₃ lvl idx left right →
      Nonempty (HashCollision256 H)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hEq
    exact ⟨⟨_, _, quorumEncodeFramed_cross_domain_ne _ _
      (Nat.lt_trans (by decide) pow256_8_gt_64)
      (Nat.lt_trans (by decide) pow256_8_gt_64) (by decide), hEq⟩⟩
  · intro hEq
    exact ⟨⟨_, _, quorumEncodeFramed_cross_domain_ne _ _
      (Nat.lt_trans (by decide) pow256_8_gt_64)
      (Nat.lt_trans (by decide) pow256_8_gt_64) (by decide), hEq⟩⟩
  · intro hEq
    exact ⟨⟨_, _, quorumEncodeFramed_cross_domain_ne _ _
      (Nat.lt_trans (by decide) pow256_8_gt_64)
      (Nat.lt_trans (by decide) pow256_8_gt_64) (by decide), hEq⟩⟩

/-- Message digest bound to `(pkSeed, root, leaf, msg)` under `"QSAG.QUORUM.MSG/v1"` (`quorum_jorts.rs:284-286`). -/
def quorumMessageHash (H : List UInt8 → Digest256)
    (pk : QuorumPublicKey) (leaf : UInt64) (msg : List UInt8) : Digest256 :=
  H (quorumEncodeFramed quorumMsgTag
      [encodeDigest256 pk.pkSeed, encodeDigest256 pk.root, encodeNatBeBytes 8 leaf.toNat, msg])

/-- Grinding digest over `(msgHash, counter)` under `"QSAG.QUORUM.DIGEST/v1"` (`quorum_jorts.rs:291`). -/
def quorumCounterDigest (H : List UInt8 → Digest256)
    (msgHash : Digest256) (counter : UInt32) : Digest256 :=
  H (quorumEncodeFramed quorumDigestTag
      [encodeDigest256 msgHash, encodeNatBeBytes 4 counter.toNat])

private theorem quorumLeafRecord_ext {r₁ r₂ : QuorumLeafRecord}
    (h1 : r₁.leaf = r₂.leaf) (h2 : r₁.msgHash = r₂.msgHash)
    (h3 : r₁.counter = r₂.counter) (h4 : r₁.digits = r₂.digits) : r₁ = r₂ := by
  cases r₁; cases r₂
  dsimp only at h1 h2 h3 h4
  subst h1 h2 h3 h4
  rfl

private theorem quorumEncodeFramed4_injective
    (domain : ByteArray) (hd : domain.data.toList.length < 256 ^ 8)
    {a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : List UInt8}
    (ha₁ : a₁.length < 256 ^ 8) (hb₁ : b₁.length < 256 ^ 8)
    (hc₁ : c₁.length < 256 ^ 8) (hd₁ : d₁.length < 256 ^ 8)
    (ha₂ : a₂.length < 256 ^ 8) (hb₂ : b₂.length < 256 ^ 8)
    (hc₂ : c₂.length < 256 ^ 8) (hd₂ : d₂.length < 256 ^ 8)
    (hEq : quorumEncodeFramed domain [a₁, b₁, c₁, d₁] =
           quorumEncodeFramed domain [a₂, b₂, c₂, d₂]) :
    a₁ = a₂ ∧ b₁ = b₂ ∧ c₁ = c₂ ∧ d₁ = d₂ := by
  simp only [quorumEncodeFramed, quorumFrameFields] at hEq
  obtain ⟨_, r1⟩ := quorumFrameField_prefix_inj hd hd hEq
  obtain ⟨ea, r2⟩ := quorumFrameField_prefix_inj ha₁ ha₂ r1
  obtain ⟨eb, r3⟩ := quorumFrameField_prefix_inj hb₁ hb₂ r2
  obtain ⟨ec, r4⟩ := quorumFrameField_prefix_inj hc₁ hc₂ r3
  obtain ⟨ed, _⟩ := quorumFrameField_prefix_inj hd₁ hd₂ r4
  exact ⟨ea, eb, ec, ed⟩

/-- Canonical framed byte preimage of `QuorumLeafRecord` under `"QSAG.QUORUM.BINDING/v1"` (`quorum_jorts.rs:333-343`). -/
def encodeQuorumLeafRecord (rec : QuorumLeafRecord) : List UInt8 :=
  quorumEncodeFramed quorumBindingTag
    [ encodeNatBeBytes 8 rec.leaf.toNat,
      encodeDigest256 rec.msgHash,
      encodeNatBeBytes 4 rec.counter.toNat,
      rec.digits ]

theorem encodeQuorumLeafRecord_injective {r₁ r₂ : QuorumLeafRecord}
    (hDig₁ : r₁.digits.length < 256 ^ 8) (hDig₂ : r₂.digits.length < 256 ^ 8)
    (hEq : encodeQuorumLeafRecord r₁ = encodeQuorumLeafRecord r₂) : r₁ = r₂ := by
  have hTagLt : quorumBindingTag.data.toList.length < 256 ^ 8 :=
    Nat.lt_trans (by decide : quorumBindingTag.data.toList.length < 64) pow256_8_gt_64
  have hLen8 : ∀ n, (encodeNatBeBytes 8 n).length < 256 ^ 8 := fun n => by
    rw [encodeNatBeBytes_length]
    exact Nat.lt_trans (by decide : 8 < 64) pow256_8_gt_64
  have hLen4 : ∀ n, (encodeNatBeBytes 4 n).length < 256 ^ 8 := fun n => by
    rw [encodeNatBeBytes_length]
    exact Nat.lt_trans (by decide : 4 < 64) pow256_8_gt_64
  have hLen32 : ∀ d, (encodeDigest256 d).length < 256 ^ 8 := fun d => by
    rw [encodeDigest256_length]
    exact Nat.lt_trans (by decide : 32 < 64) pow256_8_gt_64
  obtain ⟨hLeaf, hMh, hCtr, hDig⟩ :=
    quorumEncodeFramed4_injective quorumBindingTag hTagLt
      (hLen8 r₁.leaf.toNat) (hLen32 r₁.msgHash) (hLen4 r₁.counter.toNat) hDig₁
      (hLen8 r₂.leaf.toNat) (hLen32 r₂.msgHash) (hLen4 r₂.counter.toNat) hDig₂
      hEq
  have hLeafEq : r₁.leaf = r₂.leaf :=
    UInt64.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq
      (encodeNatBeBytes_injective
        (Nat.lt_of_lt_of_eq r₁.leaf.toBitVec.isLt pow2_64_eq_256_8)
        (Nat.lt_of_lt_of_eq r₂.leaf.toBitVec.isLt pow2_64_eq_256_8) hLeaf))
  have hMhEq := encodeDigest256_injective hMh
  have hCtrEq : r₁.counter = r₂.counter :=
    UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq
      (encodeNatBeBytes_injective
        (Nat.lt_of_lt_of_eq r₁.counter.toBitVec.isLt pow2_32_eq_256_4)
        (Nat.lt_of_lt_of_eq r₂.counter.toBitVec.isLt pow2_32_eq_256_4) hCtr))
  exact quorumLeafRecord_ext hLeafEq hMhEq hCtrEq hDig

-- Keep framing opaque to routine definitional equality; proofs unfold it explicitly.
attribute [irreducible] quorumFrameFields

/-- Leaf commitment binding under `"QSAG.QUORUM.BINDING/v1"` (`LeafRecord::binding`, `quorum_jorts.rs:333-343`). -/
def quorumLeafRecordBinding (H : List UInt8 → Digest256) (rec : QuorumLeafRecord) : Digest256 :=
  H (encodeQuorumLeafRecord rec)

/-- Constructive binding theorem for `quorumLeafRecordBinding` (`0 Classical.choice`). -/
theorem quorumLeafRecordBinding_binding (H : List UInt8 → Digest256)
    {r₁ r₂ : QuorumLeafRecord}
    (hDig₁ : r₁.digits.length < 256 ^ 8) (hDig₂ : r₂.digits.length < 256 ^ 8)
    (hBind : quorumLeafRecordBinding H r₁ = quorumLeafRecordBinding H r₂) :
    r₁ = r₂ ∨ Nonempty (HashCollision256 H) := by
  if hPre : encodeQuorumLeafRecord r₁ = encodeQuorumLeafRecord r₂ then
    exact .inl (encodeQuorumLeafRecord_injective hDig₁ hDig₂ hPre)
  else
    exact .inr ⟨⟨encodeQuorumLeafRecord r₁, encodeQuorumLeafRecord r₂, hPre, hBind⟩⟩

/-- Committee echo MAC under `"QSAG.QUORUM.ECHO.MAC/v1"` (`CommitteeCustodian::echo_for`, `quorum_jorts.rs:768-775, 954-959`). -/
def computeQuorumEchoMac
    (MAC : Digest256 → List UInt8 → Digest256)
    (pairwiseKey : Digest256) (fromParty toParty committee : Nat)
    (epoch : UInt64) (binding : Digest256) : Digest256 :=
  MAC pairwiseKey
    (quorumEncodeFramed quorumEchoMacTag
      [ encodeNatBeBytes 8 fromParty,
        encodeNatBeBytes 8 toParty,
        encodeNatBeBytes 8 committee,
        encodeNatBeBytes 8 epoch.toNat,
        encodeDigest256 binding ])

/-- Global latch acknowledgement MAC under `"QSAG.QUORUM.ACK.MAC/v1"` (`ShamirCustodian::ack`, `quorum_jorts.rs:1352-1358, 1454-1460`). -/
def computeQuorumAckMac
    (MAC : Digest256 → List UInt8 → Digest256)
    (pairwiseKey : Digest256) (fromParty toParty : Nat)
    (leaf : UInt64) (binding : Digest256) : Digest256 :=
  MAC pairwiseKey
    (quorumEncodeFramed quorumAckMacTag
      [ encodeNatBeBytes 8 fromParty,
        encodeNatBeBytes 8 toParty,
        encodeNatBeBytes 8 leaf.toNat,
        encodeDigest256 binding ])

/-- Cross-protocol MAC domain separation: `QS-A` echo MAC frames and `QS-B` ack MAC frames never collide. -/
theorem quorumEchoMac_ne_ackMac_frame
    (f₁ t₁ c₁ f₂ t₂ : Nat) (ep leaf : UInt64) (b₁ b₂ : Digest256) :
    quorumEncodeFramed quorumEchoMacTag
      [encodeNatBeBytes 8 f₁, encodeNatBeBytes 8 t₁, encodeNatBeBytes 8 c₁,
       encodeNatBeBytes 8 ep.toNat, encodeDigest256 b₁] ≠
    quorumEncodeFramed quorumAckMacTag
      [encodeNatBeBytes 8 f₂, encodeNatBeBytes 8 t₂, encodeNatBeBytes 8 leaf.toNat,
       encodeDigest256 b₂] :=
  quorumEncodeFramed_cross_domain_ne _ _
    (Nat.lt_trans (by decide) pow256_8_gt_64)
    (Nat.lt_trans (by decide) pow256_8_gt_64) (by decide)

/-- Durable WAL payload persisted atomically before memory state advances. -/
structure BeltLatchWalPayload where
  nextEpoch : Nat
  inFlight : Option BeltLatchRecord
  deriving DecidableEq, Repr

/-- Underlying physical WAL storage state (unwritten, durably persisted, or torn/corrupted). -/
inductive BeltWalDiskState where
  | unwritten
  | persisted (payload : BeltLatchWalPayload)
  | corrupted
  deriving DecidableEq, Repr

/-- Mode 3B in-memory rolling window entry (erased on crash or upon spend). -/
structure JortsStagedLeaf where
  epoch : UInt64
  spent : Bool
  deriving DecidableEq, Repr

/-- Complete per-custodian `BeltLatch` + `Jorts` Mode 3A/3B volatile and durable state. -/
structure BeltLatchNodeState where
  height : Nat
  maxWindow : Nat
  nextEpoch : Nat
  inFlight : Option BeltLatchRecord
  walPoisoned : Bool
  disk : BeltWalDiskState
  failNextPersist : Bool
  stagedWindow : List JortsStagedLeaf
  deriving DecidableEq, Repr

/-- Fresh unpoisoned custodian node at `nextEpoch = 0`. -/
def BeltLatchNodeState.init (height maxWindow : Nat) : BeltLatchNodeState where
  height := height
  maxWindow := maxWindow
  nextEpoch := 0
  inFlight := none
  walPoisoned := false
  disk := .unwritten
  failNextPersist := false
  stagedWindow := []

/-- Explicit refusal clauses of `BeltLatch` (`0` silent skips). -/
inductive BeltLatchError where
  | walPoisoned
  | epochExhausted
  | jumpWindowExceeded
  | epochConsumed
  | epochAlreadyBound
  | retrySaltMismatch
  | digitsMismatch
  | nothingBound
  | quorumTooSmall
  | missingOrInvalidPeerEcho
  | walIoFailure
  deriving DecidableEq, Repr

/-- Outcome of a `BeltLatch` bind transition (`fresh` WAL persist vs idempotent `replay`). -/
inductive BeltBindOutcome where
  | fresh
  | replay
  deriving DecidableEq, Repr

/-- Crash and recover strictly from durable `disk`:
    - Wipes volatile `stagedWindow` (Mode 3B memory-only window) and `failNextPersist`;
    - Restores `(nextEpoch, inFlight)` from `disk` if `.unwritten` or `.persisted`;
    - Latches `walPoisoned := true` permanently if `disk = .corrupted`. -/
def beltLatchCrashAndRecover (st : BeltLatchNodeState) : BeltLatchNodeState :=
  match st.disk with
  | .unwritten =>
    { st with
      nextEpoch := 0
      inFlight := none
      walPoisoned := false
      failNextPersist := false
      stagedWindow := [] }
  | .persisted pay =>
    { st with
      nextEpoch := pay.nextEpoch
      inFlight := pay.inFlight
      walPoisoned := false
      failNextPersist := false
      stagedWindow := [] }
  | .corrupted =>
    { st with
      inFlight := none
      walPoisoned := true
      failNextPersist := false
      stagedWindow := [] }

/-- Stateful `BeltLatch.bind` step with bounded jump guard (`epoch ≤ nextEpoch + maxWindow`),
    persist-precedes-memory semantics, replay idempotence, and terminal WAL-error poison latch. -/
def beltLatchBindStep (st : BeltLatchNodeState) (rec : BeltLatchRecord) :
    CustodyStepOutcome BeltLatchNodeState BeltBindOutcome BeltLatchError :=
  if st.walPoisoned then
    .rejected st .walPoisoned
  else
    match st.inFlight with
    | some cur =>
      if decide (cur.epoch = rec.epoch) then
        if !decide (cur.msgDigest = rec.msgDigest) then
          .rejected st .epochAlreadyBound
        else if !decide (cur.retrySalt = rec.retrySalt) then
          .rejected st .retrySaltMismatch
        else if !decide (cur.targetSumDigits = rec.targetSumDigits) then
          .rejected st .digitsMismatch
        else
          .accepted st .replay
      else if rec.epoch.toNat < st.nextEpoch then
        .rejected st .epochConsumed
      else if rec.epoch.toNat ≥ 2 ^ st.height then
        .rejected st .epochExhausted
      else if rec.epoch.toNat > st.nextEpoch + st.maxWindow then
        .rejected st .jumpWindowExceeded
      else if st.failNextPersist || decide (st.disk = .corrupted) then
        .rejected { st with walPoisoned := true, failNextPersist := false } .walIoFailure
      else
        let pay : BeltLatchWalPayload := { nextEpoch := rec.epoch.toNat + 1, inFlight := some rec }
        .accepted
          { st with
            nextEpoch := pay.nextEpoch
            inFlight := some rec
            disk := .persisted pay }
          .fresh
    | none =>
      if rec.epoch.toNat < st.nextEpoch then
        .rejected st .epochConsumed
      else if rec.epoch.toNat ≥ 2 ^ st.height then
        .rejected st .epochExhausted
      else if rec.epoch.toNat > st.nextEpoch + st.maxWindow then
        .rejected st .jumpWindowExceeded
      else if st.failNextPersist || decide (st.disk = .corrupted) then
        .rejected { st with walPoisoned := true, failNextPersist := false } .walIoFailure
      else
        let pay : BeltLatchWalPayload := { nextEpoch := rec.epoch.toNat + 1, inFlight := some rec }
        .accepted
          { st with
            nextEpoch := pay.nextEpoch
            inFlight := some rec
            disk := .persisted pay }
          .fresh

/-- Environment Completeness Theorem (`beltLatch_skip_implies_contract_violation`):
    Every rejection of `beltLatchBindStep` names a genuine violated precondition; no valid fresh
    or exact-replay request on an unpoisoned, uncorrupted node within `[nextEpoch, nextEpoch + maxWindow]`
    is ever skipped. -/
theorem beltLatch_skip_implies_contract_violation
    (st : BeltLatchNodeState) (rec : BeltLatchRecord) (st' : BeltLatchNodeState) (err : BeltLatchError)
    (hRej : beltLatchBindStep st rec = .rejected st' err) :
    match err with
    | .walPoisoned => st.walPoisoned = true
    | .epochAlreadyBound =>
      ∃ cur, st.inFlight = some cur ∧ cur.epoch = rec.epoch ∧ cur.msgDigest ≠ rec.msgDigest
    | .retrySaltMismatch =>
      ∃ cur, st.inFlight = some cur ∧ cur.epoch = rec.epoch ∧
        cur.msgDigest = rec.msgDigest ∧ cur.retrySalt ≠ rec.retrySalt
    | .digitsMismatch =>
      ∃ cur, st.inFlight = some cur ∧ cur.epoch = rec.epoch ∧
        cur.msgDigest = rec.msgDigest ∧ cur.retrySalt = rec.retrySalt ∧
        cur.targetSumDigits ≠ rec.targetSumDigits
    | .epochConsumed => rec.epoch.toNat < st.nextEpoch
    | .epochExhausted => 2 ^ st.height ≤ rec.epoch.toNat
    | .jumpWindowExceeded => st.nextEpoch + st.maxWindow < rec.epoch.toNat
    | .walIoFailure =>
      (st.failNextPersist = true ∨ st.disk = .corrupted) ∧
      st'.walPoisoned = true ∧ st'.inFlight = st.inFlight ∧ st'.nextEpoch = st.nextEpoch
    | _ => False := by
  unfold beltLatchBindStep at hRej
  if hPois : st.walPoisoned = true then
    simp only [hPois, ↓reduceIte] at hRej
    injection hRej with _ hErr
    subst hErr
    exact hPois
  else
    simp only [hPois, Bool.false_eq_true, ↓reduceIte] at hRej
    cases hInf : st.inFlight with
    | none =>
      simp only [hInf] at hRej
      if hCons : rec.epoch.toNat < st.nextEpoch then
        simp only [hCons, ↓reduceIte] at hRej
        injection hRej with _ hErr; subst hErr; exact hCons
      else if hExh : rec.epoch.toNat ≥ 2 ^ st.height then
        simp only [hCons, hExh, ↓reduceIte] at hRej
        injection hRej with _ hErr; subst hErr; exact hExh
      else if hJump : rec.epoch.toNat > st.nextEpoch + st.maxWindow then
        simp only [hCons, hExh, hJump, ↓reduceIte] at hRej
        injection hRej with _ hErr; subst hErr; exact hJump
      else if hIo : (st.failNextPersist || decide (st.disk = .corrupted)) = true then
        simp only [hCons, hExh, hJump, hIo, ↓reduceIte] at hRej
        injection hRej with hSt hErr; subst hSt hErr
        rcases Bool.or_eq_true_iff.mp hIo with hFail | hDisk
        · exact ⟨.inl hFail, rfl, rfl, rfl⟩
        · exact ⟨.inr (of_decide_eq_true hDisk), rfl, rfl, rfl⟩
      else
        simp only [hCons, hExh, hJump, hIo, Bool.false_eq_true, ↓reduceIte] at hRej
        cases hRej
    | some cur =>
      simp only [hInf] at hRej
      if hEqEp : decide (cur.epoch = rec.epoch) = true then
        simp only [hEqEp, ↓reduceIte] at hRej
        have hEp : cur.epoch = rec.epoch := of_decide_eq_true hEqEp
        if hMd : decide (cur.msgDigest = rec.msgDigest) = false then
          simp only [hMd, Bool.not_false, ↓reduceIte] at hRej
          injection hRej with _ hErr; subst hErr
          exact ⟨cur, rfl, hEp, of_decide_eq_false hMd⟩
        else
          have hMdT : decide (cur.msgDigest = rec.msgDigest) = true := Bool.not_eq_false _ |>.mp hMd
          if hSalt : decide (cur.retrySalt = rec.retrySalt) = false then
            simp only [hMdT, Bool.not_true, hSalt, Bool.not_false, Bool.false_eq_true, ↓reduceIte] at hRej
            injection hRej with _ hErr; subst hErr
            exact ⟨cur, rfl, hEp, of_decide_eq_true hMdT, of_decide_eq_false hSalt⟩
          else
            have hSaltT : decide (cur.retrySalt = rec.retrySalt) = true := Bool.not_eq_false _ |>.mp hSalt
            if hDig : decide (cur.targetSumDigits = rec.targetSumDigits) = false then
              simp only [hMdT, hSaltT, Bool.not_true, hDig, Bool.not_false, Bool.false_eq_true, ↓reduceIte] at hRej
              injection hRej with _ hErr; subst hErr
              exact ⟨cur, rfl, hEp, of_decide_eq_true hMdT, of_decide_eq_true hSaltT,
                of_decide_eq_false hDig⟩
            else
              have hDigT : decide (cur.targetSumDigits = rec.targetSumDigits) = true := Bool.not_eq_false _ |>.mp hDig
              simp only [hMdT, hSaltT, hDigT, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hRej
              cases hRej
      else
        simp only [hEqEp, Bool.false_eq_true, ↓reduceIte] at hRej
        if hCons : rec.epoch.toNat < st.nextEpoch then
          simp only [hCons, ↓reduceIte] at hRej
          injection hRej with _ hErr; subst hErr; exact hCons
        else if hExh : rec.epoch.toNat ≥ 2 ^ st.height then
          simp only [hCons, hExh, ↓reduceIte] at hRej
          injection hRej with _ hErr; subst hErr; exact hExh
        else if hJump : rec.epoch.toNat > st.nextEpoch + st.maxWindow then
          simp only [hCons, hExh, hJump, ↓reduceIte] at hRej
          injection hRej with _ hErr; subst hErr; exact hJump
        else if hIo : (st.failNextPersist || decide (st.disk = .corrupted)) = true then
          simp only [hCons, hExh, hJump, hIo, ↓reduceIte] at hRej
          injection hRej with hSt hErr; subst hSt hErr
          rcases Bool.or_eq_true_iff.mp hIo with hFail | hDisk
          · exact ⟨.inl hFail, rfl, rfl, rfl⟩
          · exact ⟨.inr (of_decide_eq_true hDisk), rfl, rfl, rfl⟩
        else
          simp only [hCons, hExh, hJump, hIo, Bool.false_eq_true, ↓reduceIte] at hRej
          cases hRej

/-- Crash-Replay Idempotence & Mode 3B $\to$ Mode 3A Recovery Theorem:
    After an unpoisoned custodian durably binds `rec` (`Fresh`, even with Mode 3B staged leaves in
    memory) and suffers a power-loss crash (`beltLatchCrashAndRecover`), volatile Mode 3B window
    state is cleanly wiped, the persisted `retrySalt` is recovered intact from `disk`, re-binding
    `rec` for Mode 3A fallback succeeds with `.replay` (zero extra WAL writes), and any modified
    `msgDigest'` or `retrySalt'` at `rec.epoch` is deterministically rejected! -/
theorem jorts_crash_replay_idempotent_and_mode3a_fallback
    (st stBound : BeltLatchNodeState) (rec altMsg altSalt : BeltLatchRecord)
    (hFresh : beltLatchBindStep st rec = .accepted stBound .fresh)
    (hAltMsgEp : altMsg.epoch = rec.epoch) (hAltMsgNe : altMsg.msgDigest ≠ rec.msgDigest)
    (hAltSaltEp : altSalt.epoch = rec.epoch) (hAltSaltMd : altSalt.msgDigest = rec.msgDigest)
    (hAltSaltNe : altSalt.retrySalt ≠ rec.retrySalt) :
    let stRecov := beltLatchCrashAndRecover stBound
    stRecov.stagedWindow = [] ∧
    stRecov.inFlight = some rec ∧
    stRecov.nextEpoch = rec.epoch.toNat + 1 ∧
    beltLatchBindStep stRecov rec = .accepted stRecov .replay ∧
    beltLatchBindStep stRecov altMsg = .rejected stRecov .epochAlreadyBound ∧
    beltLatchBindStep stRecov altSalt = .rejected stRecov .retrySaltMismatch := by
  have hDisk : stBound.disk = .persisted { nextEpoch := rec.epoch.toNat + 1, inFlight := some rec } := by
    unfold beltLatchBindStep at hFresh
    if hPois : st.walPoisoned = true then
      simp [hPois] at hFresh
    else
      simp only [hPois, Bool.false_eq_true, ↓reduceIte] at hFresh
      cases hInf : st.inFlight with
      | none =>
        simp only [hInf] at hFresh
        split at hFresh
        · cases hFresh
        · split at hFresh
          · cases hFresh
          · split at hFresh
            · cases hFresh
            · split at hFresh
              · cases hFresh
              · injection hFresh with hSt _; rw [← hSt]
      | some cur =>
        simp only [hInf] at hFresh
        split at hFresh
        · split at hFresh
          · cases hFresh
          · split at hFresh
            · cases hFresh
            · split at hFresh <;> cases hFresh
        · split at hFresh
          · cases hFresh
          · split at hFresh
            · cases hFresh
            · split at hFresh
              · cases hFresh
              · split at hFresh
                · cases hFresh
                · injection hFresh with hSt _; rw [← hSt]
  intro stRecov
  have hRecovEq : stRecov =
      { stBound with
        nextEpoch := rec.epoch.toNat + 1
        inFlight := some rec
        walPoisoned := false
        failNextPersist := false
        stagedWindow := [] } := by
    change beltLatchCrashAndRecover stBound = _
    rw [beltLatchCrashAndRecover, hDisk]
  refine ⟨by rw [hRecovEq], by rw [hRecovEq], by rw [hRecovEq], ?_, ?_, ?_⟩
  · rw [hRecovEq]
    unfold beltLatchBindStep
    simp
  · rw [hRecovEq]
    unfold beltLatchBindStep
    have hEpB : decide (rec.epoch = altMsg.epoch) = true := decide_eq_true hAltMsgEp.symm
    have hMdF : decide (rec.msgDigest = altMsg.msgDigest) = false :=
      decide_eq_false (fun h => hAltMsgNe h.symm)
    simp only [Bool.false_eq_true, ↓reduceIte, hEpB, hMdF, Bool.not_false]
  · rw [hRecovEq]
    unfold beltLatchBindStep
    have hEpB : decide (rec.epoch = altSalt.epoch) = true := decide_eq_true hAltSaltEp.symm
    have hMdB : decide (rec.msgDigest = altSalt.msgDigest) = true := decide_eq_true hAltSaltMd.symm
    have hSaltF : decide (rec.retrySalt = altSalt.retrySalt) = false :=
      decide_eq_false (fun h => hAltSaltNe h.symm)
    simp only [Bool.false_eq_true, ↓reduceIte, hEpB, hMdB, Bool.not_true, hSaltF, Bool.not_false]

/-- Emit a pairwise-MAC-authenticated `BeltEcho` from `sender` to `receiver` for `st.inFlight`. -/
def beltLatchEmitEcho {n : Nat}
    (H : List UInt8 → Digest256)
    (MAC : Digest256 → List UInt8 → Digest256)
    (pairwiseKey : Digest256)
    (sender receiver : Fin n) (st : BeltLatchNodeState) :
    CustodyStepOutcome BeltLatchNodeState (AuthenticatedBeltEcho n) BeltLatchError :=
  if st.walPoisoned then
    .rejected st .walPoisoned
  else
    match st.inFlight with
    | none => .rejected st .nothingBound
    | some rec =>
      .accepted st
        { sender := sender
          receiver := receiver
          record := rec
          binding := beltRecordBinding H rec
          macTag := computeBeltEchoMac MAC pairwiseKey sender receiver rec }

/-- Check that `echoes` carries a valid pairwise-MAC-authenticated `BeltEcho` from every custodian
    `s` in quorum `Q` (`Q.mem s = true`) addressed to `verifier` for `rec`. -/
def verifyQuorumEchoCertificate {n : Nat}
    (H : List UInt8 → Digest256)
    (MAC : Digest256 → List UInt8 → Digest256)
    (macKeys : Fin n → Fin n → Digest256)
    (q : Nat) (verifier : Fin n) (Q : CustodiansMask n)
    (rec : BeltLatchRecord) (echoes : List (AuthenticatedBeltEcho n)) : Bool :=
  decide (q ≤ maskCard Q) &&
  (List.finRange n).all (fun s =>
    !Q.mem s ||
      echoes.any (fun e =>
        verifyAuthenticatedBeltEcho H MAC (macKeys s verifier) s verifier rec e))

/-- Multi-turn open-world distributed `BeltLatch` network state over `n` custodians. -/
structure BeltLatchNetworkState (n : Nat) where
  nodes : Fin n → BeltLatchNodeState
  honestBoundLogs : Fin n → List BeltLatchRecord
  emittedHonestEchoes : List (AuthenticatedBeltEcho n)
  certifiedReleases : List (CustodiansMask n × Fin n × BeltLatchRecord)

/-- Fresh distributed `BeltLatch` network at epoch `0` across all `n` custodians. -/
def BeltLatchNetworkState.init (n height maxWindow : Nat) : BeltLatchNetworkState n where
  nodes := fun _ => BeltLatchNodeState.init height maxWindow
  honestBoundLogs := fun _ => []
  emittedHonestEchoes := []
  certifiedReleases := []

/-- Open-world network transitions (adversarially scheduled across arbitrary quorums, crashes,
    disk/WAL faults, retries, Mode 3B staging, and share-release authorizations). -/
inductive BeltNetworkTurn (n : Nat) where
  | honestBind (p : Fin n) (rec : BeltLatchRecord)
  | honestEmitEcho (sender receiver : Fin n)
  | crashAndRecoverNode (p : Fin n)
  | armWalPersistFault (p : Fin n)
  | corruptWalDisk (p : Fin n)
  | stageMode3BLeaf (p : Fin n) (epoch : UInt64)
  | authorizeQuorumRelease (verifier : Fin n) (Q : CustodiansMask n)
      (rec : BeltLatchRecord) (echoes : List (AuthenticatedBeltEcho n))

/-- Execute one open-world step on `BeltLatchNetworkState n` with quorum threshold `q`. -/
def stepBeltNetwork {n : Nat}
    (H : List UInt8 → Digest256)
    (MAC : Digest256 → List UInt8 → Digest256)
    (macKeys : Fin n → Fin n → Digest256)
    (Corrupt : CustodiansMask n) (q : Nat)
    (net : BeltLatchNetworkState n) (turn : BeltNetworkTurn n) : BeltLatchNetworkState n :=
  match turn with
  | .honestBind p rec =>
    if Corrupt.mem p then net
    else
      match beltLatchBindStep (net.nodes p) rec with
      | .accepted st' .fresh =>
        { net with
          nodes := fun i => if i = p then st' else net.nodes i
          honestBoundLogs := fun i => if i = p then rec :: net.honestBoundLogs p else net.honestBoundLogs i }
      | .accepted st' .replay =>
        { net with nodes := fun i => if i = p then st' else net.nodes i }
      | .rejected st' _ =>
        { net with nodes := fun i => if i = p then st' else net.nodes i }
  | .honestEmitEcho sender receiver =>
    if Corrupt.mem sender then net
    else
      match beltLatchEmitEcho H MAC (macKeys sender receiver) sender receiver (net.nodes sender) with
      | .accepted st' echo =>
        { net with
          nodes := fun i => if i = sender then st' else net.nodes i
          emittedHonestEchoes := echo :: net.emittedHonestEchoes }
      | .rejected st' _ =>
        { net with nodes := fun i => if i = sender then st' else net.nodes i }
  | .crashAndRecoverNode p =>
    if Corrupt.mem p then net
    else
      { net with nodes := fun i => if i = p then beltLatchCrashAndRecover (net.nodes p) else net.nodes i }
  | .armWalPersistFault p =>
    if Corrupt.mem p then net
    else
      let st := net.nodes p
      { net with nodes := fun i => if i = p then { st with failNextPersist := true } else net.nodes i }
  | .corruptWalDisk p =>
    if Corrupt.mem p then net
    else
      let st := net.nodes p
      { net with
        nodes := fun i =>
          if i = p then { st with disk := .corrupted, walPoisoned := true, inFlight := none }
          else net.nodes i }
  | .stageMode3BLeaf p epoch =>
    if Corrupt.mem p then net
    else
      let st := net.nodes p
      { net with
        nodes := fun i =>
          if i = p then { st with stagedWindow := ⟨epoch, false⟩ :: st.stagedWindow }
          else net.nodes i }
  | .authorizeQuorumRelease verifier Q rec echoes =>
    if Corrupt.mem verifier then net
    else
      let st := net.nodes verifier
      if !st.walPoisoned && decide (st.inFlight = some rec) &&
          verifyQuorumEchoCertificate H MAC macKeys q verifier Q rec echoes then
        { net with certifiedReleases := (Q, verifier, rec) :: net.certifiedReleases }
      else
        net

/-- Run a multi-turn open-world network trace `List (BeltNetworkTurn n)`. -/
def runBeltNetworkTrace {n : Nat}
    (H : List UInt8 → Digest256)
    (MAC : Digest256 → List UInt8 → Digest256)
    (macKeys : Fin n → Fin n → Digest256)
    (Corrupt : CustodiansMask n) (q : Nat)
    (initNet : BeltLatchNetworkState n) : List (BeltNetworkTurn n) → BeltLatchNetworkState n
  | [] => initNet
  | t :: ts =>
    runBeltNetworkTrace H MAC macKeys Corrupt q
      (stepBeltNetwork H MAC macKeys Corrupt q initNet t) ts

/-- Cryptographic pairwise MAC forgery witness: an adversary presented a valid MAC tag under an
    honest `(sender, receiver)` pair's key `(macKeys sender receiver)` for a record `rec` that
    honest `sender` never echoed to `receiver`. -/
structure PairwiseEchoMacForgery {n : Nat}
    (MAC : Digest256 → List UInt8 → Digest256)
    (macKeys : Fin n → Fin n → Digest256)
    (Corrupt : CustodiansMask n)
    (emittedHonestEchoes : List (AuthenticatedBeltEcho n)) where
  sender : Fin n
  receiver : Fin n
  honest_sender : Corrupt.mem sender = false
  honest_receiver : Corrupt.mem receiver = false
  forgedRecord : BeltLatchRecord
  forgedTag : Digest256
  valid_mac : forgedTag = computeBeltEchoMac MAC (macKeys sender receiver) sender receiver forgedRecord
  never_emitted : ∀ e ∈ emittedHonestEchoes,
    ¬ (e.sender = sender ∧ e.receiver = receiver ∧ e.record = forgedRecord)

private def PayloadCoversBoundLog (pay : BeltLatchWalPayload) (log : List BeltLatchRecord) : Prop :=
  (∀ r₁ ∈ log, ∀ r₂ ∈ log, r₁.epoch = r₂.epoch → r₁ = r₂) ∧
  (∀ r ∈ log, r.epoch.toNat < pay.nextEpoch) ∧
  (match pay.inFlight with
   | none => True
   | some cur => cur ∈ log ∧ cur.epoch.toNat < pay.nextEpoch)

private def DiskCoversBoundLog (disk : BeltWalDiskState) (log : List BeltLatchRecord) : Prop :=
  match disk with
  | .unwritten => log = []
  | .persisted pay => PayloadCoversBoundLog pay log
  | .corrupted => ∀ r₁ ∈ log, ∀ r₂ ∈ log, r₁.epoch = r₂.epoch → r₁ = r₂

private def HonestNodeWalInv (st : BeltLatchNodeState) (log : List BeltLatchRecord) : Prop :=
  DiskCoversBoundLog st.disk log ∧
  (st.walPoisoned = false →
    PayloadCoversBoundLog { nextEpoch := st.nextEpoch, inFlight := st.inFlight } log)

private def BeltNetworkInv {n : Nat} (Corrupt : CustodiansMask n) (net : BeltLatchNetworkState n) : Prop :=
  (∀ p : Fin n, Corrupt.mem p = false → HonestNodeWalInv (net.nodes p) (net.honestBoundLogs p)) ∧
  (∀ e ∈ net.emittedHonestEchoes,
    Corrupt.mem e.sender = false ∧ e.record ∈ net.honestBoundLogs e.sender)

private theorem payloadCovers_fresh_extend
    {nextEp : Nat} {inFl : Option BeltLatchRecord} {log : List BeltLatchRecord}
    {rec : BeltLatchRecord}
    (hCov : PayloadCoversBoundLog { nextEpoch := nextEp, inFlight := inFl } log)
    (hGe : nextEp ≤ rec.epoch.toNat) :
    PayloadCoversBoundLog { nextEpoch := rec.epoch.toNat + 1, inFlight := some rec } (rec :: log) := by
  rcases hCov with ⟨hUniq, hLt, _⟩
  refine ⟨?_, ?_, .head log, Nat.lt_succ_self _⟩
  · intro r₁ hr₁ r₂ hr₂ hEp
    rcases List.mem_cons.mp hr₁ with rfl | hm₁
    · rcases List.mem_cons.mp hr₂ with rfl | hm₂
      · rfl
      · have h2 : r₂.epoch.toNat < nextEp := hLt r₂ hm₂
        have hEqNat : r₁.epoch.toNat = r₂.epoch.toNat := congrArg UInt64.toNat hEp
        omega
    · rcases List.mem_cons.mp hr₂ with rfl | hm₂
      · have h1 : r₁.epoch.toNat < nextEp := hLt r₁ hm₁
        have hEqNat : r₁.epoch.toNat = r₂.epoch.toNat := congrArg UInt64.toNat hEp
        omega
      · exact hUniq r₁ hm₁ r₂ hm₂ hEp
  · intro r hr
    dsimp only
    rcases List.mem_cons.mp hr with rfl | hm
    · exact Nat.lt_succ_self _
    · have h : r.epoch.toNat < nextEp := hLt r hm
      omega

private theorem diskUniq_of_diskCovers {disk : BeltWalDiskState} {log : List BeltLatchRecord}
    (h : DiskCoversBoundLog disk log) :
    ∀ r₁ ∈ log, ∀ r₂ ∈ log, r₁.epoch = r₂.epoch → r₁ = r₂ := by
  cases disk with
  | unwritten =>
    subst h
    intro _ h1; cases h1
  | persisted pay => exact h.1
  | corrupted => exact h

private theorem honestBind_preserves_walInv
    (st : BeltLatchNodeState) (log : List BeltLatchRecord) (rec : BeltLatchRecord)
    (hInv : HonestNodeWalInv st log) :
    match beltLatchBindStep st rec with
    | .accepted st' .fresh => HonestNodeWalInv st' (rec :: log)
    | .accepted st' .replay => HonestNodeWalInv st' log
    | .rejected st' _ => HonestNodeWalInv st' log := by
  rcases hInv with ⟨hDisk, hMem⟩
  unfold beltLatchBindStep
  if hPois : st.walPoisoned = true then
    simp only [hPois, ↓reduceIte]
    exact ⟨hDisk, fun hF => by rw [hPois] at hF; cases hF⟩
  else
    have hPoisF : st.walPoisoned = false := Bool.not_eq_true _ |>.mp hPois
    have hPayMem := hMem hPoisF
    simp only [hPoisF, Bool.false_eq_true, ↓reduceIte]
    cases hInf : st.inFlight with
    | none =>
      if hCons : rec.epoch.toNat < st.nextEpoch then
        simp only [hCons, ↓reduceIte]; exact ⟨hDisk, hMem⟩
      else if hExh : rec.epoch.toNat ≥ 2 ^ st.height then
        simp only [hCons, hExh, ↓reduceIte]; exact ⟨hDisk, hMem⟩
      else if hJump : rec.epoch.toNat > st.nextEpoch + st.maxWindow then
        simp only [hCons, hExh, hJump, ↓reduceIte]; exact ⟨hDisk, hMem⟩
      else if hIo : (st.failNextPersist || decide (st.disk = .corrupted)) = true then
        simp only [hCons, hExh, hJump, hIo, ↓reduceIte]
        exact ⟨hDisk, fun hF => by cases hF⟩
      else
        simp only [hCons, hExh, hJump, hIo, Bool.false_eq_true, ↓reduceIte]
        have hGe : st.nextEpoch ≤ rec.epoch.toNat := Nat.le_of_not_gt hCons
        have hExt := payloadCovers_fresh_extend hPayMem hGe
        exact ⟨hExt, fun _ => hExt⟩
    | some cur =>
      if hEqEp : decide (cur.epoch = rec.epoch) = true then
        simp only [hEqEp, ↓reduceIte]
        if hMd : decide (cur.msgDigest = rec.msgDigest) = false then
          simp only [hMd, Bool.not_false, ↓reduceIte]; exact ⟨hDisk, hMem⟩
        else
          have hMdT : decide (cur.msgDigest = rec.msgDigest) = true := Bool.not_eq_false _ |>.mp hMd
          if hSalt : decide (cur.retrySalt = rec.retrySalt) = false then
            simp only [hMdT, Bool.not_true, hSalt, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
            exact ⟨hDisk, hMem⟩
          else
            have hSaltT : decide (cur.retrySalt = rec.retrySalt) = true := Bool.not_eq_false _ |>.mp hSalt
            if hDig : decide (cur.targetSumDigits = rec.targetSumDigits) = false then
              simp only [hMdT, hSaltT, Bool.not_true, hDig, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
              exact ⟨hDisk, hMem⟩
            else
              have hDigT : decide (cur.targetSumDigits = rec.targetSumDigits) = true := Bool.not_eq_false _ |>.mp hDig
              simp only [hMdT, hSaltT, hDigT, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
              exact ⟨hDisk, hMem⟩
      else
        simp only [hEqEp, Bool.false_eq_true, ↓reduceIte]
        if hCons : rec.epoch.toNat < st.nextEpoch then
          simp only [hCons, ↓reduceIte]; exact ⟨hDisk, hMem⟩
        else if hExh : rec.epoch.toNat ≥ 2 ^ st.height then
          simp only [hCons, hExh, ↓reduceIte]; exact ⟨hDisk, hMem⟩
        else if hJump : rec.epoch.toNat > st.nextEpoch + st.maxWindow then
          simp only [hCons, hExh, hJump, ↓reduceIte]; exact ⟨hDisk, hMem⟩
        else if hIo : (st.failNextPersist || decide (st.disk = .corrupted)) = true then
          simp only [hCons, hExh, hJump, hIo, ↓reduceIte]
          exact ⟨hDisk, fun hF => by cases hF⟩
        else
          simp only [hCons, hExh, hJump, hIo, Bool.false_eq_true, ↓reduceIte]
          have hGe : st.nextEpoch ≤ rec.epoch.toNat := Nat.le_of_not_gt hCons
          have hExt := payloadCovers_fresh_extend hPayMem hGe
          exact ⟨hExt, fun _ => hExt⟩

private theorem updateSingleNode_preserves {n : Nat}
    {nodes : Fin n → BeltLatchNodeState}
    {logs : Fin n → List BeltLatchRecord}
    {Corrupt : CustodiansMask n}
    (p : Fin n) (st' : BeltLatchNodeState)
    (hNodes : ∀ i : Fin n, Corrupt.mem i = false → HonestNodeWalInv (nodes i) (logs i))
    (hStep : HonestNodeWalInv st' (logs p)) :
    ∀ i : Fin n, Corrupt.mem i = false →
      HonestNodeWalInv (if i = p then st' else nodes i) (logs i) := by
  intro i hi
  by_cases hip : i = p
  · subst hip; simp only [↓reduceIte]; exact hStep
  · simp only [hip, ↓reduceIte]; exact hNodes i hi

private theorem stepBeltNetwork_preserves_inv {n : Nat}
    (H : List UInt8 → Digest256)
    (MAC : Digest256 → List UInt8 → Digest256)
    (macKeys : Fin n → Fin n → Digest256)
    (Corrupt : CustodiansMask n) (q : Nat)
    (net : BeltLatchNetworkState n) (turn : BeltNetworkTurn n)
    (hInv : BeltNetworkInv Corrupt net) :
    BeltNetworkInv Corrupt (stepBeltNetwork H MAC macKeys Corrupt q net turn) := by
  rcases hInv with ⟨hNodes, hEchoes⟩
  cases turn with
  | honestBind p rec =>
    unfold stepBeltNetwork
    if hCp : Corrupt.mem p = true then
      simp only [hCp, ↓reduceIte]; exact ⟨hNodes, hEchoes⟩
    else
      have hCpF : Corrupt.mem p = false := Bool.not_eq_true _ |>.mp hCp
      simp only [hCpF, Bool.false_eq_true, ↓reduceIte]
      have hStep := honestBind_preserves_walInv (net.nodes p) (net.honestBoundLogs p) rec (hNodes p hCpF)
      cases hOut : beltLatchBindStep (net.nodes p) rec with
      | accepted st' out =>
        rw [hOut] at hStep
        cases out with
        | fresh =>
          dsimp only
          refine ⟨?_, ?_⟩
          · intro i hi
            by_cases hip : i = p
            · subst hip; simp only [↓reduceIte]; exact hStep
            · simp only [hip, ↓reduceIte]; exact hNodes i hi
          · intro e he
            obtain ⟨hSe, hMemE⟩ := hEchoes e he
            refine ⟨hSe, ?_⟩
            by_cases hsp : e.sender = p
            · subst hsp; simp only [↓reduceIte, List.mem_cons]; exact .inr hMemE
            · simp only [hsp, ↓reduceIte]; exact hMemE
        | replay =>
          dsimp only at hStep ⊢
          exact ⟨updateSingleNode_preserves p st' hNodes hStep, hEchoes⟩
      | rejected st' err =>
        rw [hOut] at hStep
        dsimp only at hStep ⊢
        exact ⟨updateSingleNode_preserves p st' hNodes hStep, hEchoes⟩
  | honestEmitEcho sender receiver =>
    unfold stepBeltNetwork
    if hCs : Corrupt.mem sender = true then
      simp only [hCs, ↓reduceIte]; exact ⟨hNodes, hEchoes⟩
    else
      have hCsF : Corrupt.mem sender = false := Bool.not_eq_true _ |>.mp hCs
      simp only [hCsF, Bool.false_eq_true, ↓reduceIte]
      unfold beltLatchEmitEcho
      if hPois : (net.nodes sender).walPoisoned = true then
        simp only [hPois, ↓reduceIte]
        exact ⟨updateSingleNode_preserves sender (net.nodes sender) hNodes (hNodes sender hCsF), hEchoes⟩
      else
        have hPoisF : (net.nodes sender).walPoisoned = false := Bool.not_eq_true _ |>.mp hPois
        simp only [hPoisF, Bool.false_eq_true, ↓reduceIte]
        cases hInf : (net.nodes sender).inFlight with
        | none =>
          dsimp only
          exact ⟨updateSingleNode_preserves sender (net.nodes sender) hNodes (hNodes sender hCsF), hEchoes⟩
        | some rec =>
          dsimp only
          have hPay := (hNodes sender hCsF).2 hPoisF
          have hInLog : rec ∈ net.honestBoundLogs sender := by
            have h3 := hPay.2.2
            dsimp only at h3
            rw [hInf] at h3
            exact h3.1
          refine ⟨updateSingleNode_preserves sender (net.nodes sender) hNodes (hNodes sender hCsF), ?_⟩
          intro e he
          rcases List.mem_cons.mp he with rfl | hOld
          · exact ⟨hCsF, hInLog⟩
          · exact hEchoes e hOld
  | crashAndRecoverNode p =>
    unfold stepBeltNetwork
    if hCp : Corrupt.mem p = true then
      simp only [hCp, ↓reduceIte]; exact ⟨hNodes, hEchoes⟩
    else
      have hCpF : Corrupt.mem p = false := Bool.not_eq_true _ |>.mp hCp
      simp only [hCpF, Bool.false_eq_true, ↓reduceIte]
      have hRecovInv : HonestNodeWalInv (beltLatchCrashAndRecover (net.nodes p)) (net.honestBoundLogs p) := by
        rcases hNodes p hCpF with ⟨hDisk, _⟩
        unfold beltLatchCrashAndRecover
        cases hD : (net.nodes p).disk with
        | unwritten =>
          rw [hD] at hDisk
          change net.honestBoundLogs p = [] at hDisk
          dsimp only [HonestNodeWalInv, DiskCoversBoundLog, PayloadCoversBoundLog]
          rw [hDisk]
          exact ⟨rfl, fun _ => ⟨fun _ h => False.elim (List.not_mem_nil h),
                                fun _ h => False.elim (List.not_mem_nil h), trivial⟩⟩
        | persisted pay =>
          rw [hD] at hDisk
          exact ⟨hDisk, fun _ => hDisk⟩
        | corrupted =>
          rw [hD] at hDisk
          exact ⟨hDisk, fun hF => by cases hF⟩
      exact ⟨updateSingleNode_preserves p _ hNodes hRecovInv, hEchoes⟩
  | armWalPersistFault p =>
    unfold stepBeltNetwork
    if hCp : Corrupt.mem p = true then
      simp only [hCp, ↓reduceIte]; exact ⟨hNodes, hEchoes⟩
    else
      have hCpF : Corrupt.mem p = false := Bool.not_eq_true _ |>.mp hCp
      simp only [hCpF, Bool.false_eq_true, ↓reduceIte]
      exact ⟨updateSingleNode_preserves p _ hNodes (hNodes p hCpF), hEchoes⟩
  | corruptWalDisk p =>
    unfold stepBeltNetwork
    if hCp : Corrupt.mem p = true then
      simp only [hCp, ↓reduceIte]; exact ⟨hNodes, hEchoes⟩
    else
      have hCpF : Corrupt.mem p = false := Bool.not_eq_true _ |>.mp hCp
      simp only [hCpF, Bool.false_eq_true, ↓reduceIte]
      have hCorrInv : HonestNodeWalInv
          { net.nodes p with disk := .corrupted, walPoisoned := true, inFlight := none }
          (net.honestBoundLogs p) := by
        rcases hNodes p hCpF with ⟨hDisk, _⟩
        exact ⟨diskUniq_of_diskCovers hDisk, fun hF => by cases hF⟩
      exact ⟨updateSingleNode_preserves p _ hNodes hCorrInv, hEchoes⟩
  | stageMode3BLeaf p epoch =>
    unfold stepBeltNetwork
    if hCp : Corrupt.mem p = true then
      simp only [hCp, ↓reduceIte]; exact ⟨hNodes, hEchoes⟩
    else
      have hCpF : Corrupt.mem p = false := Bool.not_eq_true _ |>.mp hCp
      simp only [hCpF, Bool.false_eq_true, ↓reduceIte]
      exact ⟨updateSingleNode_preserves p _ hNodes (hNodes p hCpF), hEchoes⟩
  | authorizeQuorumRelease verifier Q rec echoes =>
    unfold stepBeltNetwork
    if hCv : Corrupt.mem verifier = true then
      simp only [hCv, ↓reduceIte]; exact ⟨hNodes, hEchoes⟩
    else
      have hCvF : Corrupt.mem verifier = false := Bool.not_eq_true _ |>.mp hCv
      simp only [hCvF, Bool.false_eq_true, ↓reduceIte]
      split <;> exact ⟨hNodes, hEchoes⟩

private theorem runBeltNetworkTrace_preserves_inv {n : Nat}
    (H : List UInt8 → Digest256)
    (MAC : Digest256 → List UInt8 → Digest256)
    (macKeys : Fin n → Fin n → Digest256)
    (Corrupt : CustodiansMask n) (q height maxWindow : Nat)
    (trace : List (BeltNetworkTurn n)) :
    BeltNetworkInv Corrupt
      (runBeltNetworkTrace H MAC macKeys Corrupt q
        (BeltLatchNetworkState.init n height maxWindow) trace) := by
  have hInit : BeltNetworkInv Corrupt (BeltLatchNetworkState.init n height maxWindow) := by
    refine ⟨?_, fun _ h => by cases h⟩
    intro p _
    exact ⟨rfl, fun _ => ⟨fun _ h => False.elim (List.not_mem_nil h),
                          fun _ h => False.elim (List.not_mem_nil h), trivial⟩⟩
  generalize BeltLatchNetworkState.init n height maxWindow = net₀ at hInit
  induction trace generalizing net₀ with
  | nil => exact hInit
  | cons t ts ih =>
    exact ih _ (stepBeltNetwork_preserves_inv H MAC macKeys Corrupt q net₀ t hInit)

private theorem mem_finRange_self {n : Nat} (s : Fin n) : s ∈ List.finRange n :=
  List.mem_finRange s

private def findMatchingEcho {n : Nat}
    (H : List UInt8 → Digest256)
    (MAC : Digest256 → List UInt8 → Digest256)
    (key : Digest256) (s v : Fin n) (rec : BeltLatchRecord) :
    (echoes : List (AuthenticatedBeltEcho n)) →
    echoes.any (fun e => verifyAuthenticatedBeltEcho H MAC key s v rec e) = true →
    { e : AuthenticatedBeltEcho n //
      e ∈ echoes ∧ verifyAuthenticatedBeltEcho H MAC key s v rec e = true }
  | [], h => by cases h
  | e :: es, h =>
    if he : verifyAuthenticatedBeltEcho H MAC key s v rec e = true then
      ⟨e, .head es, he⟩
    else
      have hTail : es.any (fun x => verifyAuthenticatedBeltEcho H MAC key s v rec x) = true := by
        simp only [List.any_cons, he, Bool.false_or] at h
        exact h
      let ⟨e', hm', hv'⟩ := findMatchingEcho H MAC key s v rec es hTail
      ⟨e', .tail e hm', hv'⟩

/-- **Crown Jewel 1A — `(t, n, f)` BFT Quorum-Switching `BeltLatch` Global Uniqueness
    (`beltLatch_quorum_intersection_global_uniqueness`)**:
    Across ANY multi-turn open-world network trace `trace` (with arbitrary quorum switches,
    crashes, WAL recoveries, Mode 3B staging, WAL faults, and retries), whenever `2 * q > n + f`,
    `|Corrupt| ≤ f`, and two certified latch quorums `Q1, Q2` (`|Q1| ≥ q`, `|Q2| ≥ q`) verify
    echo bundles for `(epoch, rec₁)` and `(epoch, rec₂)` at honest verifiers `v₁, v₂`
    (`rec₁.epoch = rec₂.epoch`):
    1. `|Q1 ∩ Q2| ≥ 2 * q - n ≥ f + 1`;
    2. We constructively extract an honest custodian `p ∈ (Q1 ∩ Q2) \ Corrupt`;
    3. Either `rec₁ = rec₂` (hence `(rec₁.msgDigest, rec₁.retrySalt, rec₁.targetSumDigits) =
       (rec₂.msgDigest, rec₂.retrySalt, rec₂.targetSumDigits)` globally!), OR the adversary
       exhibited an explicit `PairwiseEchoMacForgery` on an honest pair `(p, vᵢ)`! -/
theorem beltLatch_quorum_intersection_global_uniqueness {n q f height maxWindow : Nat}
    (H : List UInt8 → Digest256)
    (MAC : Digest256 → List UInt8 → Digest256)
    (macKeys : Fin n → Fin n → Digest256)
    (Corrupt Q1 Q2 : CustodiansMask n)
    (hQuorum : 2 * q > n + f)
    (hCorrupt : maskCard Corrupt ≤ f)
    (hQ1 : q ≤ maskCard Q1)
    (hQ2 : q ≤ maskCard Q2)
    (trace : List (BeltNetworkTurn n))
    (v₁ v₂ : Fin n)
    (hv₁ : Corrupt.mem v₁ = false)
    (hv₂ : Corrupt.mem v₂ = false)
    (rec₁ rec₂ : BeltLatchRecord)
    (hSameEpoch : rec₁.epoch = rec₂.epoch)
    (echoes₁ echoes₂ : List (AuthenticatedBeltEcho n))
    (hCert₁ : verifyQuorumEchoCertificate H MAC macKeys q v₁ Q1 rec₁ echoes₁ = true)
    (hCert₂ : verifyQuorumEchoCertificate H MAC macKeys q v₂ Q2 rec₂ echoes₂ = true) :
    let net := runBeltNetworkTrace H MAC macKeys Corrupt q
      (BeltLatchNetworkState.init n height maxWindow) trace
    let pWit := extractBeltHonestQuorumWitness Q1 Q2 Corrupt hQuorum hQ1 hQ2 hCorrupt
    (2 * q - n ≤ maskCard (maskInter Q1 Q2) ∧ f + 1 ≤ 2 * q - n) ∧
    (Q1.mem pWit.1 = true ∧ Q2.mem pWit.1 = true ∧ Corrupt.mem pWit.1 = false) ∧
    ((rec₁ = rec₂ ∧
      rec₁.msgDigest = rec₂.msgDigest ∧
      rec₁.retrySalt = rec₂.retrySalt ∧
      rec₁.targetSumDigits = rec₂.targetSumDigits) ∨
     Nonempty (PairwiseEchoMacForgery MAC macKeys Corrupt net.emittedHonestEchoes)) := by
  intro net pWit
  have hIE := maskCard_inter_add_n_ge Q1 Q2
  have hCardBounds : 2 * q - n ≤ maskCard (maskInter Q1 Q2) ∧ f + 1 ≤ 2 * q - n := by
    constructor <;> omega
  let p := pWit.1
  obtain ⟨hpQ1, hpQ2, hpHon⟩ := pWit.2
  refine ⟨hCardBounds, ⟨hpQ1, hpQ2, hpHon⟩, ?_⟩
  have hNetInv := runBeltNetworkTrace_preserves_inv H MAC macKeys Corrupt q height maxWindow trace
  rcases hNetInv with ⟨hNodeInvs, hEchoInvs⟩
  have hAll₁ : ((List.finRange n).all (fun s =>
      !Q1.mem s || echoes₁.any (fun e => verifyAuthenticatedBeltEcho H MAC (macKeys s v₁) s v₁ rec₁ e))) = true :=
    (Bool.and_eq_true_iff.mp hCert₁).2
  have hAll₂ : ((List.finRange n).all (fun s =>
      !Q2.mem s || echoes₂.any (fun e => verifyAuthenticatedBeltEcho H MAC (macKeys s v₂) s v₂ rec₂ e))) = true :=
    (Bool.and_eq_true_iff.mp hCert₂).2
  have hAny₁ : echoes₁.any (fun e => verifyAuthenticatedBeltEcho H MAC (macKeys p v₁) p v₁ rec₁ e) = true := by
    have hpMem := List.all_eq_true.mp hAll₁ p (mem_finRange_self p)
    rw [hpQ1] at hpMem
    exact hpMem
  have hAny₂ : echoes₂.any (fun e => verifyAuthenticatedBeltEcho H MAC (macKeys p v₂) p v₂ rec₂ e) = true := by
    have hpMem := List.all_eq_true.mp hAll₂ p (mem_finRange_self p)
    rw [hpQ2] at hpMem
    exact hpMem
  let ⟨e₁, _, hVer₁⟩ := findMatchingEcho H MAC (macKeys p v₁) p v₁ rec₁ echoes₁ hAny₁
  let ⟨e₂, _, hVer₂⟩ := findMatchingEcho H MAC (macKeys p v₂) p v₂ rec₂ echoes₂ hAny₂
  unfold verifyAuthenticatedBeltEcho at hVer₁ hVer₂
  rcases Bool.and_eq_true_iff.mp hVer₁ with ⟨_, hMac₁⟩
  rcases Bool.and_eq_true_iff.mp hVer₂ with ⟨_, hMac₂⟩
  if hEm₁ : net.emittedHonestEchoes.any
      (fun e => decide (e.sender = p) && decide (e.receiver = v₁) && decide (e.record = rec₁)) = true then
    if hEm₂ : net.emittedHonestEchoes.any
        (fun e => decide (e.sender = p) && decide (e.receiver = v₂) && decide (e.record = rec₂)) = true then
      obtain ⟨eh₁, hMemEh₁, hPred₁⟩ := List.any_eq_true.mp hEm₁
      obtain ⟨eh₂, hMemEh₂, hPred₂⟩ := List.any_eq_true.mp hEm₂
      rcases Bool.and_eq_true_iff.mp hPred₁ with ⟨hP1a, hEhRec₁⟩
      rcases Bool.and_eq_true_iff.mp hP1a with ⟨hEhS₁, _⟩
      rcases Bool.and_eq_true_iff.mp hPred₂ with ⟨hP2a, hEhRec₂⟩
      rcases Bool.and_eq_true_iff.mp hP2a with ⟨hEhS₂, _⟩
      have hInLog₁ : rec₁ ∈ net.honestBoundLogs p := by
        have h := (hEchoInvs eh₁ hMemEh₁).2
        rw [of_decide_eq_true hEhS₁, of_decide_eq_true hEhRec₁] at h
        exact h
      have hInLog₂ : rec₂ ∈ net.honestBoundLogs p := by
        have h := (hEchoInvs eh₂ hMemEh₂).2
        rw [of_decide_eq_true hEhS₂, of_decide_eq_true hEhRec₂] at h
        exact h
      have hUniq := diskUniq_of_diskCovers (hNodeInvs p hpHon).1
      have hEqRec : rec₁ = rec₂ := hUniq rec₁ hInLog₁ rec₂ hInLog₂ hSameEpoch
      exact .inl ⟨hEqRec, congrArg BeltLatchRecord.msgDigest hEqRec,
        congrArg BeltLatchRecord.retrySalt hEqRec,
        congrArg BeltLatchRecord.targetSumDigits hEqRec⟩
    else
      refine .inr ⟨{
        sender := p
        receiver := v₂
        honest_sender := hpHon
        honest_receiver := hv₂
        forgedRecord := rec₂
        forgedTag := e₂.macTag
        valid_mac := of_decide_eq_true hMac₂
        never_emitted := ?_ }⟩
      intro e he ⟨hs, hr, hrec⟩
      apply hEm₂
      exact List.any_eq_true.mpr ⟨e, he, by simp [hs, hr, hrec]⟩
  else
    refine .inr ⟨{
      sender := p
      receiver := v₁
      honest_sender := hpHon
      honest_receiver := hv₁
      forgedRecord := rec₁
      forgedTag := e₁.macTag
      valid_mac := of_decide_eq_true hMac₁
      never_emitted := ?_ }⟩
    intro e he ⟨hs, hr, hrec⟩
    apply hEm₁
    exact List.any_eq_true.mpr ⟨e, he, by simp [hs, hr, hrec]⟩

/-! ### Crown Jewel 1B — Necessity: `#tooth` Under-Threshold Quorum-Switching Double-Sign Attack -/

/-- Prefix quorum `{0, ..., q - 1}` of exact cardinality `q`. -/
def prefixQuorumMask (n q : Nat) : CustodiansMask n where
  mem i := decide (i.val < q)

/-- Suffix quorum `{n - q, ..., n - 1}` of exact cardinality `q`. -/
def suffixQuorumMask (n q : Nat) : CustodiansMask n where
  mem i := decide (n - q ≤ i.val)

private theorem maskCard_prefix : ∀ (n q : Nat), q ≤ n → maskCard (prefixQuorumMask n q) = q
  | 0, 0, _ => rfl
  | 0, _ + 1, h => by omega
  | n + 1, 0, _ => by
    have hEq : prefixQuorumMask (n + 1) 0 = emptyMask (n + 1) := by
      apply congrArg CustodiansMask.mk; funext i
      change decide (i.val < 0) = false
      simp
    rw [hEq, maskCard_empty]
  | n + 1, q + 1, h => by
    simp only [maskCard_succ, prefixQuorumMask, Nat.zero_lt_succ, decide_true, ↓reduceIte]
    have hTail : tailMask ⟨fun i : Fin (n + 1) => decide (i.val < q + 1)⟩ = prefixQuorumMask n q := by
      apply congrArg CustodiansMask.mk; funext i
      change decide (i.val + 1 < q + 1) = decide (i.val < q)
      simp [Nat.add_lt_add_iff_right]
    rw [hTail, maskCard_prefix n q (by omega)]
    omega

private theorem maskCard_ge_threshold : ∀ (n k : Nat), k ≤ n →
    maskCard ⟨fun i : Fin n => decide (k ≤ i.val)⟩ = n - k
  | 0, 0, _ => rfl
  | 0, _ + 1, h => by omega
  | n + 1, 0, _ => by
    rw [maskCard_succ]
    have h0 : ({ mem := fun i : Fin (n + 1) => decide (0 ≤ i.val) } : CustodiansMask (n + 1)).mem
        ⟨0, Nat.zero_lt_succ n⟩ = true := rfl
    have hTail : tailMask ⟨fun i : Fin (n + 1) => decide (0 ≤ i.val)⟩ =
        ⟨fun i : Fin n => decide (0 ≤ i.val)⟩ := by
      apply congrArg CustodiansMask.mk; funext i
      change decide (0 ≤ i.val + 1) = decide (0 ≤ i.val)
      simp [Nat.zero_le]
    rw [h0, hTail, maskCard_ge_threshold n 0 (Nat.zero_le n)]
    simp [Nat.add_comm]
  | n + 1, k + 1, h => by
    rw [maskCard_succ]
    have h0 : ({ mem := fun i : Fin (n + 1) => decide (k + 1 ≤ i.val) } : CustodiansMask (n + 1)).mem
        ⟨0, Nat.zero_lt_succ n⟩ = false := by
      change decide (k + 1 ≤ 0) = false
      simp
    have hTail : tailMask ⟨fun i : Fin (n + 1) => decide (k + 1 ≤ i.val)⟩ =
        ⟨fun i : Fin n => decide (k ≤ i.val)⟩ := by
      apply congrArg CustodiansMask.mk; funext i
      change decide (k + 1 ≤ i.val + 1) = decide (k ≤ i.val)
      simp [Nat.add_le_add_iff_right]
    rw [h0, hTail, maskCard_ge_threshold n k (by omega)]
    simp

/-- **`#tooth` Under-Threshold Quorum-Switching Double-Sign Theorem
    (`tooth_under_threshold_latch_quorum_switches_double_sign`)**:
    1. **General Constructive Necessity (`2 * q ≤ n + f`, `q ≤ n`)**: Constructively exhibits two
       quorums `Q1, Q2` of exact size `q` and a corrupt subset `Corrupt = Q1 ∩ Q2` of size
       `≤ f` such that every honest custodian belongs to AT MOST ONE of `{Q1, Q2}`, executes the
       real `beltLatchBindStep` + pairwise-MAC intra-quorum echo check with zero faults on its
       single session, and yet `Q1` authorizes `(epoch 0, rec₁)` while `Q2` authorizes
       `(epoch 0, rec₂)` for **distinct messages `rec₁.msgDigest ≠ rec₂.msgDigest` on the same
       leaf epoch `0`**!
    2. **Explicit Deployed Attack Witnesses**: Instantiates concrete multi-turn double-sign
       executions at BOTH **`(t = 2, n = 3, f = 1, q = 2)`** (`Q1 = {P0, P1}`, `Q2 = {P1, P2}`,
       `Corrupt = {P1}`) AND **`(t = 3, n = 5, f = 2, q = 3)`** (`Q1 = {P0, P3, P4}`,
       `Q2 = {P1, P3, P4}`, `Corrupt = {P3, P4}`), releasing certified openings for BOTH `rec₁`
       and `rec₂` on epoch `0`! -/
theorem tooth_under_threshold_latch_quorum_switches_double_sign
    (H : List UInt8 → Digest256)
    (MAC : Digest256 → List UInt8 → Digest256)
    (rec₁ rec₂ : BeltLatchRecord)
    (hEpoch0_1 : rec₁.epoch = 0)
    (hEpoch0_2 : rec₂.epoch = 0)
    (hDistinctMsg : rec₁.msgDigest ≠ rec₂.msgDigest) :
    -- Part 1: General (n, f, q) necessity whenever q ≤ n and 2 * q ≤ n + f
    (∀ (n f q : Nat) (macKeys : Fin n → Fin n → Digest256),
      q ≤ n → 2 * q ≤ n + f →
      let Q1 := prefixQuorumMask n q
      let Q2 := suffixQuorumMask n q
      let Corrupt := maskInter Q1 Q2
      maskCard Q1 = q ∧
      maskCard Q2 = q ∧
      maskCard Corrupt ≤ f ∧
      maskSub (maskInter Q1 Q2) Corrupt ∧
      (∀ p : Fin n, Corrupt.mem p = false →
        let st₀ := BeltLatchNodeState.init 20 4
        (Q1.mem p = true → Q2.mem p = false ∧
          ∃ st₁, beltLatchBindStep st₀ rec₁ = .accepted st₁ .fresh ∧
            verifyQuorumEchoCertificate H MAC macKeys q p Q1 rec₁
              ((List.finRange n).map (fun s =>
                { sender := s, receiver := p, record := rec₁,
                  binding := beltRecordBinding H rec₁,
                  macTag := computeBeltEchoMac MAC (macKeys s p) s p rec₁ })) = true) ∧
        (Q2.mem p = true → Q1.mem p = false ∧
          ∃ st₂, beltLatchBindStep st₀ rec₂ = .accepted st₂ .fresh ∧
            verifyQuorumEchoCertificate H MAC macKeys q p Q2 rec₂
              ((List.finRange n).map (fun s =>
                { sender := s, receiver := p, record := rec₂,
                  binding := beltRecordBinding H rec₂,
                  macTag := computeBeltEchoMac MAC (macKeys s p) s p rec₂ })) = true))) ∧
    -- Part 2: Concrete (t = 2, n = 3, f = 1, q = 2) multi-turn execution ({P0, P1} then {P1, P2})
    (∀ (macKeys3 : Fin 3 → Fin 3 → Digest256),
      let Q1_23 : CustodiansMask 3 := ⟨fun i => decide (i.val = 0 ∨ i.val = 1)⟩
      let Q2_23 : CustodiansMask 3 := ⟨fun i => decide (i.val = 1 ∨ i.val = 2)⟩
      let C_23  : CustodiansMask 3 := ⟨fun i => decide (i.val = 1)⟩
      let p0 : Fin 3 := ⟨0, by decide⟩
      let p2 : Fin 3 := ⟨2, by decide⟩
      let echoes1 := (List.finRange 3).map (fun s =>
        ({ sender := s, receiver := p0, record := rec₁,
           binding := beltRecordBinding H rec₁,
           macTag := computeBeltEchoMac MAC (macKeys3 s p0) s p0 rec₁ } : AuthenticatedBeltEcho 3))
      let echoes2 := (List.finRange 3).map (fun s =>
        ({ sender := s, receiver := p2, record := rec₂,
           binding := beltRecordBinding H rec₂,
           macTag := computeBeltEchoMac MAC (macKeys3 s p2) s p2 rec₂ } : AuthenticatedBeltEcho 3))
      let netFinal := runBeltNetworkTrace H MAC macKeys3 C_23 2
        (BeltLatchNetworkState.init 3 20 4)
        [.honestBind p0 rec₁, .authorizeQuorumRelease p0 Q1_23 rec₁ echoes1,
         .honestBind p2 rec₂, .authorizeQuorumRelease p2 Q2_23 rec₂ echoes2]
      maskCard Q1_23 = 2 ∧ maskCard Q2_23 = 2 ∧ maskCard C_23 = 1 ∧
      (Q1_23, p0, rec₁) ∈ netFinal.certifiedReleases ∧
      (Q2_23, p2, rec₂) ∈ netFinal.certifiedReleases ∧
      rec₁.msgDigest ≠ rec₂.msgDigest) ∧
    -- Part 3: Concrete (t = 3, n = 5, f = 2, q = 3) multi-turn execution ({P0, P3, P4} then {P1, P3, P4})
    (∀ (macKeys5 : Fin 5 → Fin 5 → Digest256),
      let Q1_35 : CustodiansMask 5 := ⟨fun i => decide (i.val = 0 ∨ i.val = 3 ∨ i.val = 4)⟩
      let Q2_35 : CustodiansMask 5 := ⟨fun i => decide (i.val = 1 ∨ i.val = 3 ∨ i.val = 4)⟩
      let C_35  : CustodiansMask 5 := ⟨fun i => decide (i.val = 3 ∨ i.val = 4)⟩
      let p0 : Fin 5 := ⟨0, by decide⟩
      let p1 : Fin 5 := ⟨1, by decide⟩
      let echoes1 := (List.finRange 5).map (fun s =>
        ({ sender := s, receiver := p0, record := rec₁,
           binding := beltRecordBinding H rec₁,
           macTag := computeBeltEchoMac MAC (macKeys5 s p0) s p0 rec₁ } : AuthenticatedBeltEcho 5))
      let echoes2 := (List.finRange 5).map (fun s =>
        ({ sender := s, receiver := p1, record := rec₂,
           binding := beltRecordBinding H rec₂,
           macTag := computeBeltEchoMac MAC (macKeys5 s p1) s p1 rec₂ } : AuthenticatedBeltEcho 5))
      let netFinal := runBeltNetworkTrace H MAC macKeys5 C_35 3
        (BeltLatchNetworkState.init 5 20 4)
        [.honestBind p0 rec₁, .authorizeQuorumRelease p0 Q1_35 rec₁ echoes1,
         .honestBind p1 rec₂, .authorizeQuorumRelease p1 Q2_35 rec₂ echoes2]
      maskCard Q1_35 = 3 ∧ maskCard Q2_35 = 3 ∧ maskCard C_35 = 2 ∧
      (Q1_35, p0, rec₁) ∈ netFinal.certifiedReleases ∧
      (Q2_35, p1, rec₂) ∈ netFinal.certifiedReleases ∧
      rec₁.msgDigest ≠ rec₂.msgDigest) := by
  have hEp1Nat : rec₁.epoch.toNat = 0 := by rw [hEpoch0_1]; rfl
  have hEp2Nat : rec₂.epoch.toNat = 0 := by rw [hEpoch0_2]; rfl
  let st₁ : BeltLatchNodeState :=
    { BeltLatchNodeState.init 20 4 with
      nextEpoch := 1
      inFlight := some rec₁
      disk := .persisted { nextEpoch := 1, inFlight := some rec₁ } }
  let st₂ : BeltLatchNodeState :=
    { BeltLatchNodeState.init 20 4 with
      nextEpoch := 1
      inFlight := some rec₂
      disk := .persisted { nextEpoch := 1, inFlight := some rec₂ } }
  have hB1 : beltLatchBindStep (BeltLatchNodeState.init 20 4) rec₁ = .accepted st₁ .fresh := by
    dsimp only [beltLatchBindStep, BeltLatchNodeState.init, st₁]
    simp [hEp1Nat]
  have hB2 : beltLatchBindStep (BeltLatchNodeState.init 20 4) rec₂ = .accepted st₂ .fresh := by
    dsimp only [beltLatchBindStep, BeltLatchNodeState.init, st₂]
    simp [hEp2Nat]
  have hCertMap : ∀ {m : Nat} (q : Nat) (mk : Fin m → Fin m → Digest256) (v : Fin m)
      (Q : CustodiansMask m) (rec : BeltLatchRecord),
      q ≤ maskCard Q →
      verifyQuorumEchoCertificate H MAC mk q v Q rec
        ((List.finRange m).map (fun s =>
          { sender := s, receiver := v, record := rec,
            binding := beltRecordBinding H rec,
            macTag := computeBeltEchoMac MAC (mk s v) s v rec })) = true := by
    intro m q mk v Q rec hQCard
    unfold verifyQuorumEchoCertificate
    rw [Bool.and_eq_true_iff]
    refine ⟨decide_eq_true hQCard, List.all_eq_true.mpr ?_⟩
    intro s _
    cases hQs : Q.mem s
    · simp
    · simp only [Bool.not_true, Bool.false_or]
      apply List.any_eq_true.mpr
      refine ⟨{ sender := s, receiver := v, record := rec,
                binding := beltRecordBinding H rec,
                macTag := computeBeltEchoMac MAC (mk s v) s v rec },
              List.mem_map.mpr ⟨s, mem_finRange_self s, rfl⟩, ?_⟩
      unfold verifyAuthenticatedBeltEcho
      simp
  refine ⟨?_, ?_, ?_⟩
  · -- Part 1
    intro n f q macKeys hqLe hUnder Q1 Q2 Corrupt
    have hCard1 : maskCard Q1 = q := maskCard_prefix n q hqLe
    have hCard2 : maskCard Q2 = q := by
      have hSuf := maskCard_ge_threshold n (n - q) (Nat.sub_le n q)
      change maskCard ⟨fun i : Fin n => decide (n - q ≤ i.val)⟩ = q
      rw [hSuf]
      omega
    have hCardC : maskCard Corrupt ≤ f := by
      have hSub : Corrupt = maskInter Q1 Q2 := rfl
      rw [hSub]
      have hInterZeroOrEq : ∀ (m a b : Nat),
          a ≤ b → maskCard ⟨fun i : Fin m => decide (i.val < a) && decide (b ≤ i.val)⟩ = 0 := by
        intro m a b hab
        have hEmp : (⟨fun i : Fin m => decide (i.val < a) && decide (b ≤ i.val)⟩ : CustodiansMask m) =
            emptyMask m := by
          apply congrArg CustodiansMask.mk; funext i
          change (decide (i.val < a) && decide (b ≤ i.val)) = false
          simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
          by_cases hi : i.val < a
          · right; omega
          · left; exact hi
        rw [hEmp, maskCard_empty]
      by_cases hDisj : q ≤ n - q
      · have hInterDef : maskInter Q1 Q2 =
            ⟨fun i : Fin n => decide (i.val < q) && decide (n - q ≤ i.val)⟩ := rfl
        rw [hInterDef, hInterZeroOrEq n q (n - q) hDisj]
        exact Nat.zero_le f
      · -- When n - q < q, Q1 ∪ Q2 covers all n elements, or even simpler:
        have hCover : (⟨fun i : Fin n => Q1.mem i || Q2.mem i⟩ : CustodiansMask n) =
            ⟨fun i : Fin n => decide (0 ≤ i.val)⟩ := by
          apply congrArg CustodiansMask.mk; funext i
          simp only [Q1, Q2, prefixQuorumMask, suffixQuorumMask, Nat.zero_le, decide_true, Bool.or_eq_true, decide_eq_true_eq]
          omega
        have hUI := maskCard_union_inter Q1 Q2
        rw [hCover, maskCard_ge_threshold n 0 (Nat.zero_le n), Nat.sub_zero, hCard1, hCard2] at hUI
        omega
    refine ⟨hCard1, hCard2, hCardC, fun _ h => h, ?_⟩
    intro p hpHon
    constructor
    · intro hpQ1
      have hpNotQ2 : Q2.mem p = false := by
        cases h2 : Q2.mem p
        · rfl
        · have hBoth : Corrupt.mem p = true := by
            change (Q1.mem p && Q2.mem p) = true
            rw [hpQ1, h2]; rfl
          rw [hpHon] at hBoth; cases hBoth
      exact ⟨hpNotQ2, st₁, hB1, hCertMap q macKeys p Q1 rec₁ (by omega)⟩
    · intro hpQ2
      have hpNotQ1 : Q1.mem p = false := by
        cases h1 : Q1.mem p
        · rfl
        · have hBoth : Corrupt.mem p = true := by
            change (Q1.mem p && Q2.mem p) = true
            rw [h1, hpQ2]; rfl
          rw [hpHon] at hBoth; cases hBoth
      exact ⟨hpNotQ1, st₂, hB2, hCertMap q macKeys p Q2 rec₂ (by omega)⟩
  · -- Part 2: (t = 2, n = 3, f = 1, q = 2)
    intro macKeys3 Q1_23 Q2_23 C_23 p0 p2 echoes1 echoes2 netFinal
    have hC1 : maskCard Q1_23 = 2 := by decide
    have hC2 : maskCard Q2_23 = 2 := by decide
    have hCC : maskCard C_23 = 1 := by decide
    have hV1 := hCertMap 2 macKeys3 p0 Q1_23 rec₁ (by rw [hC1]; exact Nat.le_refl 2)
    have hV2 := hCertMap 2 macKeys3 p2 Q2_23 rec₂ (by rw [hC2]; exact Nat.le_refl 2)
    have hP0Hon : C_23.mem p0 = false := by decide
    have hP2Hon : C_23.mem p2 = false := by decide
    have hP2NeP0 : p2 ≠ p0 := by decide
    have hP1 : st₁.walPoisoned = false := rfl
    have hI1 : st₁.inFlight = some rec₁ := rfl
    have hP2 : st₂.walPoisoned = false := rfl
    have hI2 : st₂.inFlight = some rec₂ := rfl
    have hRel : netFinal.certifiedReleases = [(Q2_23, p2, rec₂), (Q1_23, p0, rec₁)] := by
      change (runBeltNetworkTrace H MAC macKeys3 C_23 2 (BeltLatchNetworkState.init 3 20 4) _).certifiedReleases = _
      dsimp only [runBeltNetworkTrace, stepBeltNetwork, BeltLatchNetworkState.init, echoes1, echoes2]
      simp only [hP0Hon, hP2Hon, Bool.false_eq_true, ↓reduceIte, hB1, hP1, hI1,
        decide_true, Bool.not_false, Bool.true_and, hV1, hP2NeP0, hB2, hP2, hI2, hV2]
    refine ⟨hC1, hC2, hCC, ?_, ?_, hDistinctMsg⟩
    · rw [hRel]; exact .tail _ (.head _)
    · rw [hRel]; exact .head _
  · -- Part 3: (t = 3, n = 5, f = 2, q = 3)
    intro macKeys5 Q1_35 Q2_35 C_35 p0 p1 echoes1 echoes2 netFinal
    have hC1 : maskCard Q1_35 = 3 := by decide
    have hC2 : maskCard Q2_35 = 3 := by decide
    have hCC : maskCard C_35 = 2 := by decide
    have hV1 := hCertMap 3 macKeys5 p0 Q1_35 rec₁ (by rw [hC1]; exact Nat.le_refl 3)
    have hV2 := hCertMap 3 macKeys5 p1 Q2_35 rec₂ (by rw [hC2]; exact Nat.le_refl 3)
    have hP0Hon : C_35.mem p0 = false := by decide
    have hP1Hon : C_35.mem p1 = false := by decide
    have hP1NeP0 : p1 ≠ p0 := by decide
    have hP1 : st₁.walPoisoned = false := rfl
    have hI1 : st₁.inFlight = some rec₁ := rfl
    have hP2 : st₂.walPoisoned = false := rfl
    have hI2 : st₂.inFlight = some rec₂ := rfl
    have hRel : netFinal.certifiedReleases = [(Q2_35, p1, rec₂), (Q1_35, p0, rec₁)] := by
      change (runBeltNetworkTrace H MAC macKeys5 C_35 3 (BeltLatchNetworkState.init 5 20 4) _).certifiedReleases = _
      dsimp only [runBeltNetworkTrace, stepBeltNetwork, BeltLatchNetworkState.init, echoes1, echoes2]
      simp only [hP0Hon, hP1Hon, Bool.false_eq_true, ↓reduceIte, hB1, hP1, hI1,
        decide_true, Bool.not_false, Bool.true_and, hV1, hP1NeP0, hB2, hP2, hI2, hV2]
    refine ⟨hC1, hC2, hCC, ?_, ?_, hDistinctMsg⟩
    · rw [hRel]; exact .tail _ (.head _)
    · rw [hRel]; exact .head _

/-! ### Crown Jewel 1C — Availability Characterization & Bounded-Jump Anti-Exhaustion -/

/-- **Availability Characterization (`beltLatch_safe_and_live_iff_n_ge_3f_plus_1`)**:
    A quorum threshold `q` simultaneously satisfying BFT quorum-intersection safety
    (`2 * q > n + f`) and `f`-fault non-blocking availability (`q ≤ n - f`) exists **if and only
    if `n ≥ 3 * f + 1`**. In particular, `(n = 3, f = 1)` and `(n = 5, f = 2)` admit NO safe and
    `f`-fault-live global-tree latch quorum, whereas `(n = 7, f = 2)` succeeds at `q = 5`. -/
theorem beltLatch_safe_and_live_iff_n_ge_3f_plus_1 (n f : Nat) :
    ((∃ q : Nat, 2 * q > n + f ∧ q ≤ n - f) ↔ 3 * f + 1 ≤ n) ∧
    (¬ ∃ q : Nat, 2 * q > 3 + 1 ∧ q ≤ 3 - 1) ∧
    (¬ ∃ q : Nat, 2 * q > 5 + 2 ∧ q ≤ 5 - 2) ∧
    (2 * 5 > 7 + 2 ∧ 5 ≤ 7 - 2) := by
  refine ⟨?_, ?_, ?_, by decide⟩
  · constructor
    · rintro ⟨q, hSafe, hLive⟩
      omega
    · intro hGe
      exact ⟨(n + f) / 2 + 1, by omega, by omega⟩
  · rintro ⟨q, h1, h2⟩; omega
  · rintro ⟨q, h1, h2⟩; omega

/-- Unbounded `BeltLatch.bind` variant (omitting `epoch ≤ nextEpoch + maxWindow`, checking only
    `epoch < 2 ^ height`). -/
def beltLatchUnboundedBindStep (st : BeltLatchNodeState) (rec : BeltLatchRecord) :
    CustodyStepOutcome BeltLatchNodeState BeltBindOutcome BeltLatchError :=
  beltLatchBindStep { st with maxWindow := 2 ^ st.height } rec

/-- **`#tooth` Unbounded Epoch-Jump Tree Exhaustion (`tooth_unbounded_epoch_jump_exhausts_tree`)**:
    1. **Attack without `maxWindow`**: Starting from a fresh tree of height `h` (`1 ≤ h ≤ 62`,
       `2^h` leaves), a SINGLE unbounded request at `epoch = 2^h - 1` succeeds and sets
       `nextEpoch = 2^h`, permanently burning all `2^h - 1` skipped leaves (`∀ e < 2^h - 1`, any
       subsequent bind at `e` is rejected with `.epochConsumed` and every `e ≥ 2^h` is rejected
       with `.epochExhausted`)!
    2. **Defense with `epoch ≤ nextEpoch + maxWindow`**: When `maxWindow < 2^h - 1`, the guarded
       `beltLatchBindStep` immediately rejects `epoch = 2^h - 1` from `nextEpoch = 0` with
       `.jumpWindowExceeded`, preserving `nextEpoch = 0` and all `2^h` unburned leaves! -/
theorem tooth_unbounded_epoch_jump_exhausts_tree
    (h maxWin : Nat) (hhPos : 1 ≤ h) (hhCap : h ≤ 62)
    (hWinSmall : maxWin + 1 < 2 ^ h)
    (md salt : Digest256) (digits : List UInt8) :
    have hPowLt64 : 2 ^ h - 1 < 2 ^ 64 := by
      have hle : 2 ^ h ≤ 2 ^ 62 := Nat.pow_le_pow_right (by decide) hhCap
      omega
    let maxEp : UInt64 := UInt64.ofNatLT (2 ^ h - 1) hPowLt64
    let attackRec : BeltLatchRecord :=
      { epoch := maxEp, msgDigest := md, retrySalt := salt, targetSumDigits := digits }
    let st₀ := BeltLatchNodeState.init h maxWin
    (beltLatchBindStep st₀ attackRec = .rejected st₀ .jumpWindowExceeded ∧ st₀.nextEpoch = 0) ∧
    (∃ stExhausted,
      beltLatchUnboundedBindStep st₀ attackRec = .accepted stExhausted .fresh ∧
      stExhausted.nextEpoch = 2 ^ h ∧
      ∀ (other : BeltLatchRecord),
        other.epoch ≠ maxEp →
        (other.epoch.toNat < 2 ^ h →
          beltLatchUnboundedBindStep stExhausted other = .rejected stExhausted .epochConsumed) ∧
        (2 ^ h ≤ other.epoch.toNat →
          beltLatchUnboundedBindStep stExhausted other = .rejected stExhausted .epochExhausted)) := by
  intro hPowLt64 maxEp attackRec st₀
  have hPowPos : 1 ≤ 2 ^ h := by
    have := Nat.pow_le_pow_right (by decide : 0 < 2) hhPos
    omega
  have hMaxEpToNat : maxEp.toNat = 2 ^ h - 1 := rfl
  have hNotLt0 : ¬ maxEp.toNat < 0 := Nat.not_lt_zero _
  have hNotGe : ¬ maxEp.toNat ≥ 2 ^ h := by rw [hMaxEpToNat]; omega
  refine ⟨?_, ?_⟩
  · refine ⟨?_, rfl⟩
    dsimp only [st₀, attackRec, BeltLatchNodeState.init, beltLatchBindStep]
    simp [hNotLt0, hNotGe]
    omega
  · let stEx : BeltLatchNodeState :=
      { height := h
        maxWindow := 2 ^ h
        nextEpoch := 2 ^ h
        inFlight := some attackRec
        walPoisoned := false
        disk := .persisted { nextEpoch := 2 ^ h, inFlight := some attackRec }
        failNextPersist := false
        stagedWindow := [] }
    refine ⟨stEx, ?_, rfl, ?_⟩
    · have hAdd1 : maxEp.toNat + 1 = 2 ^ h := by rw [hMaxEpToNat]; omega
      dsimp only [beltLatchUnboundedBindStep, st₀, attackRec, BeltLatchNodeState.init, beltLatchBindStep, stEx]
      simp [hNotLt0, hNotGe, hAdd1]
      omega
    · intro other hNeMax
      have hEqB : decide (attackRec.epoch = other.epoch) = false :=
        decide_eq_false (fun he => hNeMax he.symm)
      constructor
      · intro hLt
        dsimp only [beltLatchUnboundedBindStep, beltLatchBindStep, stEx]
        simp only [Bool.false_eq_true, ↓reduceIte, hEqB, hLt]
      · intro hGe
        have hNotLt : ¬ other.epoch.toNat < 2 ^ h := Nat.not_lt.mpr hGe
        have hGe' : other.epoch.toNat ≥ 2 ^ h := hGe
        dsimp only [beltLatchUnboundedBindStep, beltLatchBindStep, stEx]
        simp only [Bool.false_eq_true, ↓reduceIte, hEqB, hNotLt, hGe']

/-! ## §2. Committee-Partitioned `t`-of-`t` Subtree Escape (`2f + 1` Safe & Live!) -/

private theorem nodup_map_inj {α β : Type} {f : α → β}
    (hf : ∀ x y, f x = f y → x = y) : ∀ {l : List α}, l.Nodup → (l.map f).Nodup
  | [], _ => .nil
  | a :: l, h => by
    obtain ⟨hNotMem, hTail⟩ := List.nodup_cons.mp h
    refine List.Pairwise.cons ?_ (nodup_map_inj hf hTail)
    intro y hy hEq
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    have hax := hf a x hEq
    subst hax
    exact hNotMem hx

/-- Constructive enumeration of all `t`-custodian subcommittees of `Fin n` (`0 Classical.choice`). -/
def chooseMasks : (n t : Nat) → List (CustodiansMask n)
  | 0, 0 => [⟨fun i => Fin.elim0 i⟩]
  | 0, _ + 1 => []
  | n + 1, 0 => (chooseMasks n 0).map (consMask false)
  | n + 1, t + 1 =>
    (chooseMasks n t).map (consMask true) ++ (chooseMasks n (t + 1)).map (consMask false)

theorem chooseMasks_card :
    ∀ (n t : Nat) {Q : CustodiansMask n}, Q ∈ chooseMasks n t → maskCard Q = t
  | 0, 0, _, _ => rfl
  | 0, _ + 1, _, h => by cases h
  | n + 1, 0, Q, h => by
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp h
    rw [maskCard_consMask, chooseMasks_card n 0 hm]
    rfl
  | n + 1, t + 1, Q, h => by
    rcases List.mem_append.mp h with hT | hF
    · obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hT
      rw [maskCard_consMask, chooseMasks_card n t hm]
      simp [Nat.add_comm]
    · obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hF
      rw [maskCard_consMask, chooseMasks_card n (t + 1) hm]
      simp

theorem mem_chooseMasks_of_card :
    ∀ (n : Nat) (Q : CustodiansMask n), Q ∈ chooseMasks n (maskCard Q)
  | 0, Q => by
    simp only [maskCard_zero, chooseMasks, List.mem_singleton]
    apply congrArg CustodiansMask.mk
    funext i; exact Fin.elim0 i
  | n + 1, Q => by
    have ih := mem_chooseMasks_of_card n (tailMask Q)
    have hEta := consMask_head_tail Q
    cases h0 : Q.mem ⟨0, Nat.zero_lt_succ n⟩
    · rw [h0] at hEta
      have hCardEq : maskCard Q = maskCard (tailMask Q) := by
        rw [maskCard_succ, h0]; simp
      cases htc : maskCard (tailMask Q) with
      | zero =>
        rw [htc] at ih hCardEq
        rw [hCardEq, ← hEta]
        exact List.mem_map.mpr ⟨tailMask Q, ih, rfl⟩
      | succ k =>
        rw [htc] at ih hCardEq
        rw [hCardEq, ← hEta]
        exact List.mem_append.mpr (.inr (List.mem_map.mpr ⟨tailMask Q, ih, rfl⟩))
    · rw [h0] at hEta
      have hCardEq : maskCard Q = maskCard (tailMask Q) + 1 := by
        rw [maskCard_succ, h0]
        simp [Nat.add_comm]
      rw [hCardEq, ← hEta]
      exact List.mem_append.mpr (.inl (List.mem_map.mpr ⟨tailMask Q, ih, rfl⟩))

theorem chooseMasks_nodup : ∀ (n t : Nat), (chooseMasks n t).Nodup
  | 0, 0 => List.Pairwise.cons (fun _ h => by cases h) .nil
  | 0, _ + 1 => .nil
  | n + 1, 0 =>
    nodup_map_inj (fun _ _ h => (consMask_inj h).2) (chooseMasks_nodup n 0)
  | n + 1, t + 1 => by
    rw [chooseMasks, List.nodup_append]
    refine ⟨nodup_map_inj (fun _ _ h => (consMask_inj h).2) (chooseMasks_nodup n t),
            nodup_map_inj (fun _ _ h => (consMask_inj h).2) (chooseMasks_nodup n (t + 1)), ?_⟩
    intro a ha b hb hEq
    obtain ⟨ma, _, rfl⟩ := List.mem_map.mp ha
    obtain ⟨mb, _, rfl⟩ := List.mem_map.mp hb
    have hbEq := (consMask_inj hEq).1
    cases hbEq

/-- Deployed committee counts: `(2, 3)` yields `3` subtrees; `(3, 5)` yields `10` subtrees. -/
theorem chooseMasks_deployed_counts :
    (chooseMasks 3 2).length = 3 ∧ (chooseMasks 5 3).length = 10 := by
  decide

/-- Constructive subcommittee selector (`0 Classical.choice`): given `t ≤ maskCard avail`,
    computes an explicit `t`-member committee `Q ⊆ avail`. -/
def selectSubcommittee : {n : Nat} → (t : Nat) → (avail : CustodiansMask n) →
    t ≤ maskCard avail →
    { Q : CustodiansMask n // maskCard Q = t ∧ maskSub Q avail }
  | n, 0, _, _ => ⟨emptyMask n, maskCard_empty n, fun _ h => by cases h⟩
  | 0, _ + 1, _, hLe => False.elim (by simp [maskCard_zero] at hLe)
  | n + 1, t + 1, avail, hLe =>
    if h0 : avail.mem ⟨0, Nat.zero_lt_succ n⟩ = true then
      have hTailLe : t ≤ maskCard (tailMask avail) := by
        simp only [maskCard_succ, h0, ↓reduceIte] at hLe
        omega
      let ⟨Qt, hCardQt, hSubQt⟩ := selectSubcommittee t (tailMask avail) hTailLe
      ⟨consMask true Qt,
       by rw [maskCard_consMask, hCardQt]; simp [Nat.add_comm],
       by
         intro i hi
         cases i with
         | mk val isLt =>
           cases val with
           | zero => exact h0
           | succ k => exact hSubQt ⟨k, Nat.lt_of_succ_lt_succ isLt⟩ hi⟩
    else
      have h0f : avail.mem ⟨0, Nat.zero_lt_succ n⟩ = false := Bool.not_eq_true _ |>.mp h0
      have hTailLe : t + 1 ≤ maskCard (tailMask avail) := by
        simp only [maskCard_succ, h0f, Bool.false_eq_true, ↓reduceIte, Nat.zero_add] at hLe
        exact hLe
      let ⟨Qt, hCardQt, hSubQt⟩ := selectSubcommittee (t + 1) (tailMask avail) hTailLe
      ⟨consMask false Qt,
       by rw [maskCard_consMask, hCardQt]; simp,
       by
         intro i hi
         cases i with
         | mk val isLt =>
           cases val with
           | zero => cases hi
           | succ k => exact hSubQt ⟨k, Nat.lt_of_succ_lt_succ isLt⟩ hi⟩

/-- Global Merkle leaf index assigned to `(committeeIdx, localEpoch)` under disjoint partitioning. -/
@[expose] def committeeGlobalLeaf (leavesPerCommittee committeeIdx localEpoch : Nat) : Nat :=
  committeeIdx * leavesPerCommittee + localEpoch

theorem committee_leaf_ranges_disjoint {leavesPerCommittee c₁ c₂ e₁ e₂ : Nat}
    (he₁ : e₁ < leavesPerCommittee) (he₂ : e₂ < leavesPerCommittee)
    (hEq : committeeGlobalLeaf leavesPerCommittee c₁ e₁ =
           committeeGlobalLeaf leavesPerCommittee c₂ e₂) :
    c₁ = c₂ ∧ e₁ = e₂ := by
  unfold committeeGlobalLeaf at hEq
  have hc : c₁ = c₂ := by
    by_cases hlt : c₁ < c₂
    · have hMul : (c₁ + 1) * leavesPerCommittee ≤ c₂ * leavesPerCommittee :=
        Nat.mul_le_mul_right leavesPerCommittee hlt
      rw [Nat.add_mul, Nat.one_mul] at hMul
      omega
    · by_cases hgt : c₂ < c₁
      · have hMul : (c₂ + 1) * leavesPerCommittee ≤ c₁ * leavesPerCommittee :=
          Nat.mul_le_mul_right leavesPerCommittee hgt
        rw [Nat.add_mul, Nat.one_mul] at hMul
        omega
      · omega
  subst hc
  exact ⟨rfl, by omega⟩

/-- Canonical ordered list of member indices `i : Fin n` of `Q` (`length = maskCard Q`). -/
def maskMembers : {n : Nat} → (Q : CustodiansMask n) → List (Fin n)
  | 0, _ => []
  | n + 1, Q =>
    let rest := (maskMembers (tailMask Q)).map (fun i => ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)
    if Q.mem ⟨0, Nat.zero_lt_succ n⟩ then ⟨0, Nat.zero_lt_succ n⟩ :: rest else rest

theorem maskMembers_length : ∀ {n : Nat} (Q : CustodiansMask n),
    (maskMembers Q).length = maskCard Q
  | 0, _ => rfl
  | n + 1, Q => by
    simp only [maskMembers, maskCard_succ]
    cases Q.mem ⟨0, Nat.zero_lt_succ n⟩ <;>
      simp [List.length_map, maskMembers_length (tailMask Q)] <;> omega

theorem mem_maskMembers_iff : ∀ {n : Nat} (Q : CustodiansMask n) (p : Fin n),
    p ∈ maskMembers Q ↔ Q.mem p = true
  | 0, _, p => Fin.elim0 p
  | n + 1, Q, ⟨0, _⟩ => by
    simp only [maskMembers]
    cases h0 : Q.mem ⟨0, Nat.zero_lt_succ n⟩
    · simp only [Bool.false_eq_true, ↓reduceIte, iff_false]
      intro hm
      obtain ⟨j, _, hjEq⟩ := List.mem_map.mp hm
      cases congrArg Fin.val hjEq
    · simp
  | n + 1, Q, ⟨k + 1, hk⟩ => by
    simp only [maskMembers]
    have ih := mem_maskMembers_iff (tailMask Q) ⟨k, Nat.lt_of_succ_lt_succ hk⟩
    cases h0 : Q.mem ⟨0, Nat.zero_lt_succ n⟩
    · simp only [Bool.false_eq_true, ↓reduceIte]
      constructor
      · intro hm
        obtain ⟨j, hjMem, hjEq⟩ := List.mem_map.mp hm
        have hjk : j = ⟨k, Nat.lt_of_succ_lt_succ hk⟩ :=
          Fin.ext (Nat.succ.inj (congrArg Fin.val hjEq))
        subst hjk
        exact ih.mp hjMem
      · intro hMem
        exact List.mem_map.mpr ⟨⟨k, Nat.lt_of_succ_lt_succ hk⟩, ih.mpr hMem, rfl⟩
    · simp only [↓reduceIte, List.mem_cons]
      constructor
      · rintro (hZero | hm)
        · cases congrArg Fin.val hZero
        · obtain ⟨j, hjMem, hjEq⟩ := List.mem_map.mp hm
          have hjk : j = ⟨k, Nat.lt_of_succ_lt_succ hk⟩ :=
            Fin.ext (Nat.succ.inj (congrArg Fin.val hjEq))
          subst hjk
          exact ih.mp hjMem
      · intro hMem
        exact .inr (List.mem_map.mpr ⟨⟨k, Nat.lt_of_succ_lt_succ hk⟩, ih.mpr hMem, rfl⟩)

theorem maskMembers_nodup : ∀ {n : Nat} (Q : CustodiansMask n), (maskMembers Q).Nodup
  | 0, _ => .nil
  | n + 1, Q => by
    simp only [maskMembers]
    have hMapNodup :
        ((maskMembers (tailMask Q)).map (fun i : Fin n => (⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ : Fin (n + 1)))).Nodup :=
      nodup_map_inj (fun a b h => Fin.ext (Nat.succ.inj (congrArg Fin.val h)))
        (maskMembers_nodup (tailMask Q))
    cases Q.mem ⟨0, Nat.zero_lt_succ n⟩
    · exact hMapNodup
    · simp only [↓reduceIte]
      refine List.Pairwise.cons ?_ hMapNodup
      intro x hx hEq
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
      cases congrArg Fin.val hEq

/-- XOR-sum of a `Fin m`-indexed family of 256-bit words. -/
def xorFin256 : (m : Nat) → (Fin m → Digest256) → Digest256
  | 0, _ => 0#256
  | m + 1, f => f ⟨0, Nat.zero_lt_succ m⟩ ^^^ xorFin256 m (fun i => f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)

private theorem bv256_xor_assoc (a b c : Digest256) : (a ^^^ b) ^^^ c = a ^^^ (b ^^^ c) := by
  apply BitVec.eq_of_getLsbD_eq; intro i _
  simp only [BitVec.getLsbD_xor]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.getLsbD i <;> rfl

private theorem bv256_xor_comm (a b : Digest256) : a ^^^ b = b ^^^ a := by
  apply BitVec.eq_of_getLsbD_eq; intro i _
  simp only [BitVec.getLsbD_xor]
  cases a.getLsbD i <;> cases b.getLsbD i <;> rfl

private theorem bv256_xor_self (a : Digest256) : a ^^^ a = 0#256 := by
  apply BitVec.eq_of_getLsbD_eq; intro i _
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_zero]
  cases a.getLsbD i <;> rfl

private theorem bv256_xor_zero (a : Digest256) : a ^^^ 0#256 = a := by
  apply BitVec.eq_of_getLsbD_eq; intro i _
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_zero]
  cases a.getLsbD i <;> rfl

private theorem bv256_zero_xor (a : Digest256) : 0#256 ^^^ a = a := by
  apply BitVec.eq_of_getLsbD_eq; intro i _
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_zero]
  cases a.getLsbD i <;> rfl

private theorem bv256_xor_cancel_right (a b : Digest256) : (a ^^^ b) ^^^ b = a := by
  rw [bv256_xor_assoc, bv256_xor_self, bv256_xor_zero]

private theorem xorFin256_update_delta :
    ∀ (m : Nat) (tape : Fin m → Digest256) (kStar : Fin m) (delta : Digest256),
      xorFin256 m (fun k => if k = kStar then tape k ^^^ delta else tape k) =
        xorFin256 m tape ^^^ delta
  | 0, _, kStar, _ => Fin.elim0 kStar
  | m + 1, tape, ⟨0, _⟩, delta => by
    simp only [xorFin256, ↓reduceIte]
    have hTail :
        xorFin256 m (fun i : Fin m =>
          if (⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ : Fin (m + 1)) = ⟨0, Nat.zero_lt_succ m⟩
          then tape ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ ^^^ delta
          else tape ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩) =
        xorFin256 m (fun i => tape ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩) := by
      apply congrArg (xorFin256 m)
      funext i
      simp
    rw [hTail, bv256_xor_assoc, bv256_xor_comm delta _, ← bv256_xor_assoc]
  | m + 1, tape, ⟨k + 1, hk⟩, delta => by
    have h0Ne : (⟨0, Nat.zero_lt_succ m⟩ : Fin (m + 1)) ≠ ⟨k + 1, hk⟩ :=
      fun h => by cases congrArg Fin.val h
    simp only [xorFin256, h0Ne, ↓reduceIte]
    have hShift :
        (fun i : Fin m =>
          if (⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ : Fin (m + 1)) = ⟨k + 1, hk⟩
          then tape ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ ^^^ delta
          else tape ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩) =
        (fun i : Fin m =>
          if i = ⟨k, Nat.lt_of_succ_lt_succ hk⟩
          then tape ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ ^^^ delta
          else tape ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩) := by
      funext i
      by_cases hik : i.1 = k
      · have h2 : i = ⟨k, Nat.lt_of_succ_lt_succ hk⟩ := Fin.ext hik
        subst h2
        simp
      · have h1 : (⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ : Fin (m + 1)) ≠ ⟨k + 1, hk⟩ :=
          fun he => hik (Nat.succ.inj (congrArg Fin.val he))
        have h2 : i ≠ ⟨k, Nat.lt_of_succ_lt_succ hk⟩ :=
          fun he => hik (congrArg Fin.val he)
        simp only [h1, h2, ↓reduceIte]
    rw [hShift, xorFin256_update_delta m _ ⟨k, Nat.lt_of_succ_lt_succ hk⟩ delta, bv256_xor_assoc]

/-- Canonical `t`-of-`t` XOR share dealer over `Fin t`: first `t - 1` slots carry uniform masks
    `tape`, and slot `t - 1` carries `secret ^^^ xorFin256 (t - 1) tape`. -/
def dealAdditiveShares (t : Nat) (secret : Digest256) (tape : Fin (t - 1) → Digest256) :
    Fin t → Digest256 :=
  fun j =>
    if h : j.val < t - 1 then
      tape ⟨j.val, h⟩
    else
      secret ^^^ xorFin256 (t - 1) tape

theorem reconstruct_dealAdditiveShares :
    ∀ (t : Nat) (_hPos : 0 < t) (secret : Digest256) (tape : Fin (t - 1) → Digest256),
      xorFin256 t (dealAdditiveShares t secret tape) = secret := by
  intro t hPos secret tape
  cases t with
  | zero => exact False.elim (Nat.lt_irrefl 0 hPos)
  | succ m =>
    have hSplit : ∀ (k : Nat) (g : Fin k → Digest256) (lastVal : Digest256),
        xorFin256 (k + 1) (fun j => if h : j.val < k then g ⟨j.val, h⟩ else lastVal) =
          xorFin256 k g ^^^ lastVal := by
      intro k
      induction k with
      | zero =>
        intro g lastVal
        simp only [xorFin256, Nat.not_lt_zero, ↓reduceDIte, bv256_xor_zero, bv256_zero_xor]
      | succ k ih =>
        intro g lastVal
        rw [xorFin256]
        have hHead : (if h : (⟨0, Nat.zero_lt_succ (k + 1)⟩ : Fin (k + 2)).val < k + 1
            then g ⟨(⟨0, Nat.zero_lt_succ (k + 1)⟩ : Fin (k + 2)).val, h⟩
            else lastVal) = g ⟨0, Nat.zero_lt_succ k⟩ := rfl
        have hTail :
            (fun i : Fin (k + 1) =>
              if h : (⟨i.val + 1, Nat.succ_lt_succ i.2⟩ : Fin (k + 2)).val < k + 1
              then g ⟨(⟨i.val + 1, Nat.succ_lt_succ i.2⟩ : Fin (k + 2)).val, h⟩
              else lastVal) =
            (fun i : Fin (k + 1) =>
              if h : i.val < k then g ⟨i.val + 1, Nat.succ_lt_succ h⟩ else lastVal) := by
          funext i
          dsimp only
          by_cases hi : i.val < k
          · have hi1 : i.val + 1 < k + 1 := Nat.succ_lt_succ hi
            simp only [hi, hi1, ↓reduceDIte]
          · have hi1 : ¬ i.val + 1 < k + 1 := fun h => hi (Nat.lt_of_succ_lt_succ h)
            simp only [hi, hi1, ↓reduceDIte]
        rw [hHead, hTail, ih (fun i => g ⟨i.val + 1, Nat.succ_lt_succ i.2⟩) lastVal, ← bv256_xor_assoc]
        rfl
    change xorFin256 (m + 1) (fun j => if h : j.val < m then tape ⟨j.val, h⟩ else secret ^^^ xorFin256 m tape) = secret
    rw [hSplit m tape (secret ^^^ xorFin256 m tape),
        bv256_xor_comm secret (xorFin256 m tape), ← bv256_xor_assoc,
        bv256_xor_self, bv256_zero_xor]

private def memberPositionAux {n : Nat} (p : Fin n) : List (Fin n) → Option Nat
  | [] => none
  | x :: xs =>
    if x = p then some 0
    else (memberPositionAux p xs).map Nat.succ

private theorem memberPositionAux_lt {n : Nat} (p : Fin n) :
    ∀ (xs : List (Fin n)) {idx : Nat}, memberPositionAux p xs = some idx → idx < xs.length
  | [], _, h => by cases h
  | x :: xs, idx, h => by
    simp only [memberPositionAux] at h
    if hx : x = p then
      simp only [hx, ↓reduceIte, Option.some.injEq] at h
      subst h; exact Nat.zero_lt_succ _
    else
      simp only [hx, ↓reduceIte, Option.map_eq_some_iff] at h
      obtain ⟨k, hk, rfl⟩ := h
      exact Nat.succ_lt_succ (memberPositionAux_lt p xs hk)

private theorem memberPositionAux_some_of_mem {n : Nat} (p : Fin n) :
    ∀ (xs : List (Fin n)), p ∈ xs → ∃ idx, memberPositionAux p xs = some idx
  | [], h => by cases h
  | x :: xs, h => by
    simp only [memberPositionAux]
    if hx : x = p then
      exact ⟨0, by simp [hx]⟩
    else
      rcases List.mem_cons.mp h with rfl | hTail
      · exact False.elim (hx rfl)
      · obtain ⟨k, hk⟩ := memberPositionAux_some_of_mem p xs hTail
        exact ⟨k + 1, by simp [hx, hk]⟩

private theorem memberPositionAux_inj {n : Nat} {p₁ p₂ : Fin n} :
    ∀ (xs : List (Fin n)) {idx : Nat},
      memberPositionAux p₁ xs = some idx →
      memberPositionAux p₂ xs = some idx →
      p₁ = p₂
  | [], _, h1, _ => by cases h1
  | x :: xs, idx, h1, h2 => by
    simp only [memberPositionAux] at h1 h2
    by_cases hx1 : x = p₁
    · simp only [hx1, ↓reduceIte, Option.some.injEq] at h1
      subst h1
      by_cases hx2 : x = p₂
      · exact hx1.symm.trans hx2
      · simp only [hx2, ↓reduceIte, Option.map_eq_some_iff] at h2
        obtain ⟨_, _, hSucc⟩ := h2
        cases hSucc
    · simp only [hx1, ↓reduceIte, Option.map_eq_some_iff] at h1
      obtain ⟨k₁, hk₁, rfl⟩ := h1
      by_cases hx2 : x = p₂
      · simp only [hx2, ↓reduceIte, Option.some.injEq] at h2
        cases h2
      · simp only [hx2, ↓reduceIte, Option.map_eq_some_iff] at h2
        obtain ⟨k₂, hk₂, hEqS⟩ := h2
        have hkEq : k₁ = k₂ := Nat.succ.inj hEqS.symm
        subst hkEq
        exact memberPositionAux_inj xs hk₁ hk₂

/-- Exclusive `t`-of-`t` subtree share held by custodian `p : Fin n` for committee `Q`
    (non-dependently matched so case-splits rewrite cleanly): `some share_j` if `p` is the `j`-th
    member of `Q`, and `none` if `p ∉ Q`. -/
def committeeCustodianShare {n : Nat} (t : Nat) (Q : CustodiansMask n)
    (secret : Digest256) (tape : Fin (t - 1) → Digest256) (p : Fin n) : Option Digest256 :=
  match memberPositionAux p (maskMembers Q) with
  | none => none
  | some idx =>
    if hLt : idx < t then
      some (dealAdditiveShares t secret tape ⟨idx, hLt⟩)
    else
      none

/-- Complete view of a subset `Viewer : CustodiansMask n` into committee `Q`'s `t`-of-`t` leaf shares. -/
def committeeViewerObservation {n : Nat} (t : Nat) (Q Viewer : CustodiansMask n)
    (secret : Digest256) (tape : Fin (t - 1) → Digest256) : Fin n → Option Digest256 :=
  fun p => if Viewer.mem p then committeeCustodianShare t Q secret tape p else none

/-- Involutive `SimpleEquiv` on `(Fin (t - 1) → Digest256)` shifting `secret₁ ↦ secret₂` while
    fixing every `t`-of-`t` share EXCEPT missing slot `missingSlot : Fin t` (`0 Classical.choice`). -/
def committeeAdditiveRebalanceEquiv (t : Nat) (missingSlot : Fin t)
    (secret₁ secret₂ : Digest256) :
    SimpleEquiv (Fin (t - 1) → Digest256) (Fin (t - 1) → Digest256) where
  toFun tape :=
    if h : missingSlot.val < t - 1 then
      fun k => if k = ⟨missingSlot.val, h⟩ then tape k ^^^ (secret₁ ^^^ secret₂) else tape k
    else
      tape
  invFun tape :=
    if h : missingSlot.val < t - 1 then
      fun k => if k = ⟨missingSlot.val, h⟩ then tape k ^^^ (secret₁ ^^^ secret₂) else tape k
    else
      tape
  left_inv tape := by
    by_cases h : missingSlot.val < t - 1
    · simp only [h, ↓reduceDIte]
      funext k
      by_cases hk : k = ⟨missingSlot.val, h⟩
      · simp only [hk, ↓reduceIte, bv256_xor_cancel_right]
      · simp only [hk, ↓reduceIte]
    · simp only [h, ↓reduceDIte]
  right_inv tape := by
    by_cases h : missingSlot.val < t - 1
    · simp only [h, ↓reduceDIte]
      funext k
      by_cases hk : k = ⟨missingSlot.val, h⟩
      · simp only [hk, ↓reduceIte, bv256_xor_cancel_right]
      · simp only [hk, ↓reduceIte]
    · simp only [h, ↓reduceDIte]

private theorem dealAdditiveShares_rebalance_other (t : Nat) (missingSlot j : Fin t)
    (hNe : j ≠ missingSlot) (secret₁ secret₂ : Digest256) (tape : Fin (t - 1) → Digest256) :
    dealAdditiveShares t secret₂
      ((committeeAdditiveRebalanceEquiv t missingSlot secret₁ secret₂).toFun tape) j =
      dealAdditiveShares t secret₁ tape j := by
  unfold dealAdditiveShares committeeAdditiveRebalanceEquiv
  dsimp only
  by_cases hMissLt : missingSlot.val < t - 1
  · simp only [hMissLt, ↓reduceDIte]
    by_cases hjLt : j.val < t - 1
    · simp only [hjLt, ↓reduceDIte]
      have hkNe : (⟨j.val, hjLt⟩ : Fin (t - 1)) ≠ ⟨missingSlot.val, hMissLt⟩ := by
        intro he
        have hv : j.val = missingSlot.val := Fin.mk.inj he
        exact hNe (Fin.ext hv)
      simp only [hkNe, ↓reduceIte]
    · simp only [hjLt, ↓reduceDIte,
        xorFin256_update_delta (t - 1) tape ⟨missingSlot.val, hMissLt⟩ (secret₁ ^^^ secret₂)]
      rw [bv256_xor_comm secret₁ secret₂,
          ← bv256_xor_assoc (xorFin256 (t - 1) tape) secret₂ secret₁,
          ← bv256_xor_assoc secret₂ (xorFin256 (t - 1) tape ^^^ secret₂) secret₁,
          bv256_xor_comm secret₂ (xorFin256 (t - 1) tape ^^^ secret₂),
          bv256_xor_cancel_right]
      exact bv256_xor_comm _ _
  · simp only [hMissLt, ↓reduceDIte]
    by_cases hjLt : j.val < t - 1
    · simp only [hjLt, ↓reduceDIte]
    · exfalso
      have hMissEq : missingSlot.val = t - 1 := by omega
      have hjEq : j.val = t - 1 := by omega
      exact hNe (Fin.ext (hjEq.trans hMissEq.symm))

private theorem finSum_zero_fn : ∀ (g : Fin 0 → Nat), finSum 0 g = 0 := by
  intro g
  have h : finSum 0 g = finSum 0 (fun _ => 0) := finSum_congr (fun i => Fin.elim0 i)
  rw [h, finSum_const]

private theorem finSum_mul_right {k : Nat} (c : Nat) (f : Fin k → Nat) :
    finSum k (fun j => f j * c) = finSum k f * c := by
  induction c with
  | zero =>
    have h0 : finSum k (fun _ => 0) = 0 := (finSum_const k 0).trans (Nat.mul_zero k)
    simp only [Nat.mul_zero, h0]
  | succ c ih =>
    have hStep : (fun j : Fin k => f j * (c + 1)) = (fun j => f j * c + f j) := by
      funext j; exact Nat.mul_succ (f j) c
    rw [finSum_congr (fun j => congrFun hStep j), finSum_add, ih, Nat.mul_succ]

/-- Constructive permutation invariance of `finSum`: any `SimpleEquiv (Fin M) (Fin M)` preserves
    exact counting sums (`0` statistical distance). -/
theorem finSum_comp_simpleEquiv :
    ∀ (M : Nat) (bij : SimpleEquiv (Fin M) (Fin M)) (w : Fin M → Nat),
      finSum M (fun i => w (bij.toFun i)) = finSum M w := by
  intro M bij w
  have hPointwise : ∀ i : Fin M,
      w (bij.toFun i) = finSum M (fun j => if j = bij.toFun i then w j else 0) := by
    intro i
    have hScale :
        finSum M (fun j => if j = bij.toFun i then w j else 0) =
        finSum M (fun j => (if j = bij.toFun i then 1 else 0) * w (bij.toFun i)) := by
      apply finSum_congr
      intro j
      by_cases hj : j = bij.toFun i
      · subst hj; simp
      · simp [hj]
    rw [hScale, finSum_mul_right, finSum_eq_indicator, Nat.one_mul]
  have hSwap : ∀ (a b : Nat) (g : Fin a → Fin b → Nat),
      finSum a (fun i => finSum b (fun j => g i j)) =
      finSum b (fun j => finSum a (fun i => g i j)) := by
    intro a
    -- Prove by induction on an auxiliary masked prefix sum on `a` using only `finSum_add` & `finSum_eq_indicator`!
    have hMask : ∀ (m : Nat), m ≤ a → ∀ (b : Nat) (g : Fin a → Fin b → Nat),
        finSum a (fun i => if decide (i.val < m) then finSum b (fun j => g i j) else 0) =
        finSum b (fun j => finSum a (fun i => if decide (i.val < m) then g i j else 0)) := by
      intro m
      induction m with
      | zero =>
        intro _ b g
        have hL : finSum a (fun _ => 0) = 0 := (finSum_const a 0).trans (Nat.mul_zero a)
        have hB : finSum b (fun _ => 0) = 0 := (finSum_const b 0).trans (Nat.mul_zero b)
        have hL' : finSum a (fun i : Fin a => if decide (i.val < 0) then finSum b (fun j => g i j) else 0) =
            finSum a (fun _ => 0) := finSum_congr (fun _ => rfl)
        have hR' : finSum b (fun j : Fin b => finSum a (fun i : Fin a => if decide (i.val < 0) then g i j else 0)) =
            finSum b (fun _ => finSum a (fun _ => 0)) :=
          finSum_congr (fun _ => finSum_congr (fun _ => rfl))
        rw [hL', hR', hL, hB]
      | succ m ih =>
        intro hmLe b g
        have hmLt : m < a := hmLe
        let im : Fin a := ⟨m, hmLt⟩
        have hDecomp : ∀ (F : Fin a → Nat) (i : Fin a),
            (if decide (i.val < m + 1) then F i else 0) =
            (if decide (i.val < m) then F i else 0) + (if i = im then F im else 0) := by
          intro F i
          by_cases hLtM : i.val < m
          · have hLtM1 : i.val < m + 1 := by omega
            have hNeIm : i ≠ im := fun he => by have := congrArg Fin.val he; dsimp [im] at this; omega
            simp [hLtM, hLtM1, hNeIm]
          · by_cases hEqM : i.val = m
            · have hiIm : i = im := Fin.ext hEqM
              subst hiIm
              have hLtM1 : im.val < m + 1 := Nat.lt_succ_self m
              have hNotM : ¬ im.val < m := Nat.lt_irrefl m
              simp [hLtM1, hNotM]
            · have hNotM1 : ¬ i.val < m + 1 := by omega
              have hNeIm : i ≠ im := fun he => hEqM (congrArg Fin.val he)
              simp [hLtM, hNotM1, hNeIm]
        have hOnePoint : ∀ (v : Nat),
            finSum a (fun i => if i = im then v else 0) = v := by
          intro v
          have hSc : (fun i : Fin a => if i = im then v else 0) =
              (fun i => (if i = im then 1 else 0) * v) := by
            funext i; by_cases hi : i = im <;> simp [hi]
          rw [finSum_congr (fun i => congrFun hSc i), finSum_mul_right, finSum_eq_indicator, Nat.one_mul]
        rw [finSum_congr (fun i => hDecomp (fun k => finSum b (fun j => g k j)) i),
            finSum_add, ih (Nat.le_of_lt hmLt) b g, hOnePoint]
        have hRHS :
            finSum b (fun j => finSum a (fun i => if decide (i.val < m + 1) then g i j else 0)) =
            finSum b (fun j =>
              finSum a (fun i => if decide (i.val < m) then g i j else 0) +
              finSum a (fun i => if i = im then g im j else 0)) := by
          apply finSum_congr
          intro j
          rw [← finSum_add]
          exact finSum_congr (fun i => hDecomp (fun k => g k j) i)
        rw [hRHS, finSum_add]
        congr 1
        exact finSum_congr (fun j => (hOnePoint (g im j)).symm)
    intro b g
    have hFull := hMask a (Nat.le_refl a) b g
    have hSimpL : finSum a (fun i : Fin a => if decide (i.val < a) then finSum b (fun j => g i j) else 0) =
        finSum a (fun i => finSum b (fun j => g i j)) :=
      finSum_congr (fun i => by simp [i.isLt])
    have hSimpR : finSum b (fun j : Fin b => finSum a (fun i : Fin a => if decide (i.val < a) then g i j else 0)) =
        finSum b (fun j => finSum a (fun i => g i j)) :=
      finSum_congr (fun _ => finSum_congr (fun i => by simp [i.isLt]))
    rw [← hSimpL, ← hSimpR]
    exact hFull
  rw [finSum_congr hPointwise, hSwap]
  apply finSum_congr
  intro j
  have hRewrite :
      (fun i : Fin M => if j = bij.toFun i then w j else 0) =
      (fun i : Fin M => (if i = bij.invFun j then 1 else 0) * w j) := by
    funext i
    by_cases hij : i = bij.invFun j
    · subst hij
      rw [bij.right_inv]
      simp
    · have hNe : j ≠ bij.toFun i := fun he => hij (by rw [he, bij.left_inv])
      simp [hij, hNe]
  rw [finSum_congr (fun i => congrFun hRewrite i), finSum_mul_right, finSum_eq_indicator, Nat.one_mul]

/-! ### Multi-Turn `QuorumJortsTurn` Committee-Partitioned (`QS-A`) & Global-Quorum (`QS-B`) State Machine -/

private def maskPositionAux {n : Nat} (target : CustodiansMask n) : List (CustodiansMask n) → Option Nat
  | [] => none
  | x :: xs =>
    if x = target then some 0
    else (maskPositionAux target xs).map Nat.succ

private theorem maskPositionAux_lt {n : Nat} (target : CustodiansMask n) :
    ∀ (xs : List (CustodiansMask n)) {idx : Nat},
      maskPositionAux target xs = some idx → idx < xs.length
  | [], _, h => by cases h
  | x :: xs, idx, h => by
    simp only [maskPositionAux] at h
    if hx : x = target then
      simp only [hx, ↓reduceIte, Option.some.injEq] at h
      subst h; exact Nat.zero_lt_succ _
    else
      simp only [hx, ↓reduceIte, Option.map_eq_some_iff] at h
      obtain ⟨k, hk, rfl⟩ := h
      exact Nat.succ_lt_succ (maskPositionAux_lt target xs hk)

private theorem maskPositionAux_mem {n : Nat} (target : CustodiansMask n) :
    ∀ (xs : List (CustodiansMask n)) {idx : Nat},
      maskPositionAux target xs = some idx → target ∈ xs
  | [], _, h => by cases h
  | x :: xs, _, h => by
    simp only [maskPositionAux] at h
    if hx : x = target then
      subst hx; exact .head xs
    else
      simp only [hx, ↓reduceIte, Option.map_eq_some_iff] at h
      obtain ⟨_, hk, _⟩ := h
      exact .tail x (maskPositionAux_mem target xs hk)

private theorem maskPositionAux_some_of_mem {n : Nat} (target : CustodiansMask n) :
    ∀ (xs : List (CustodiansMask n)), target ∈ xs → ∃ idx, maskPositionAux target xs = some idx
  | [], h => by cases h
  | x :: xs, h => by
    simp only [maskPositionAux]
    if hx : x = target then
      exact ⟨0, by simp [hx]⟩
    else
      rcases List.mem_cons.mp h with rfl | hTail
      · exact False.elim (hx rfl)
      · obtain ⟨k, hk⟩ := maskPositionAux_some_of_mem target xs hTail
        exact ⟨k + 1, by simp [hx, hk]⟩

private theorem maskPositionAux_inj {n : Nat} {Q₁ Q₂ : CustodiansMask n} :
    ∀ (xs : List (CustodiansMask n)) {idx : Nat},
      maskPositionAux Q₁ xs = some idx →
      maskPositionAux Q₂ xs = some idx →
      Q₁ = Q₂
  | [], _, h1, _ => by cases h1
  | x :: xs, idx, h1, h2 => by
    simp only [maskPositionAux] at h1 h2
    by_cases hx1 : x = Q₁
    · simp only [hx1, ↓reduceIte, Option.some.injEq] at h1
      subst h1
      by_cases hx2 : x = Q₂
      · exact hx1.symm.trans hx2
      · simp only [hx2, ↓reduceIte, Option.map_eq_some_iff] at h2
        obtain ⟨_, _, hSucc⟩ := h2
        cases hSucc
    · simp only [hx1, ↓reduceIte, Option.map_eq_some_iff] at h1
      obtain ⟨k₁, hk₁, rfl⟩ := h1
      by_cases hx2 : x = Q₂
      · simp only [hx2, ↓reduceIte, Option.some.injEq] at h2
        cases h2
      · simp only [hx2, ↓reduceIte, Option.map_eq_some_iff] at h2
        obtain ⟨k₂, hk₂, hEqS⟩ := h2
        have hkEq : k₁ = k₂ := Nat.succ.inj hEqS.symm
        subst hkEq
        exact maskPositionAux_inj xs hk₁ hk₂

/-- Constructive index of `t`-committee `Q` inside `chooseMasks n t`
    (`CommitteeLayout::committee_index`, `quorum_jorts.rs:661-666`). -/
def committeeIndexOf {n : Nat} (t : Nat) (Q : CustodiansMask n) : Option Nat :=
  maskPositionAux Q (chooseMasks n t)

theorem committeeIndexOf_lt {n t cIdx : Nat} {Q : CustodiansMask n}
    (h : committeeIndexOf t Q = some cIdx) : cIdx < (chooseMasks n t).length :=
  maskPositionAux_lt Q (chooseMasks n t) h

theorem committeeIndexOf_card {n t cIdx : Nat} {Q : CustodiansMask n}
    (h : committeeIndexOf t Q = some cIdx) : maskCard Q = t :=
  chooseMasks_card n t (maskPositionAux_mem Q (chooseMasks n t) h)

theorem committeeIndexOf_some_of_card {n t : Nat} {Q : CustodiansMask n}
    (hCard : maskCard Q = t) : ∃ cIdx, committeeIndexOf t Q = some cIdx := by
  have hMem : Q ∈ chooseMasks n t := by
    have hm := mem_chooseMasks_of_card n Q
    rw [hCard] at hm
    exact hm
  exact maskPositionAux_some_of_mem Q (chooseMasks n t) hMem

theorem committeeIndexOf_inj {n t cIdx : Nat} {Q₁ Q₂ : CustodiansMask n}
    (h₁ : committeeIndexOf t Q₁ = some cIdx)
    (h₂ : committeeIndexOf t Q₂ = some cIdx) : Q₁ = Q₂ :=
  maskPositionAux_inj (chooseMasks n t) h₁ h₂

/-- Public inverse mapping a global leaf index back to its owning committee index
    (`CommitteeLayout::committee_of_leaf`, `quorum_jorts.rs:673-677`). -/
def committeeOfLeaf (leavesPerCommittee numCommittees globalLeaf : Nat) : Option Nat :=
  if globalLeaf / leavesPerCommittee < numCommittees then
    some (globalLeaf / leavesPerCommittee)
  else
    none

theorem committeeOfLeaf_committeeGlobalLeaf
    {leavesPerCommittee numCommittees cIdx localEpoch : Nat}
    (hLpcPos : 0 < leavesPerCommittee)
    (hcLt : cIdx < numCommittees)
    (heLt : localEpoch < leavesPerCommittee) :
    committeeOfLeaf leavesPerCommittee numCommittees
      (committeeGlobalLeaf leavesPerCommittee cIdx localEpoch) = some cIdx := by
  unfold committeeGlobalLeaf committeeOfLeaf
  have hDiv : (cIdx * leavesPerCommittee + localEpoch) / leavesPerCommittee = cIdx := by
    rw [Nat.mul_comm cIdx leavesPerCommittee, Nat.mul_add_div hLpcPos,
        Nat.div_eq_of_lt heLt, Nat.add_zero]
  simp [hDiv, hcLt]

/-- Full custodian mask `{0, ..., n - 1}` of cardinality `n` (single global committee for `QS-B`). -/
def fullCustodiansMask (n : Nat) : CustodiansMask n := ⟨fun _ => true⟩

theorem maskCard_fullCustodiansMask (n : Nat) : maskCard (fullCustodiansMask n) = n := by
  have hEq : fullCustodiansMask n = prefixQuorumMask n n := by
    unfold fullCustodiansMask prefixQuorumMask
    apply congrArg CustodiansMask.mk; funext i
    exact (decide_eq_true i.isLt).symm
  rw [hEq]
  exact maskCard_prefix n n (Nat.le_refl n)

/-- Authenticated committee `LatchEcho` message (`quorum_jorts.rs:760-766`) under `"QSAG.QUORUM.ECHO.MAC/v1"`. -/
structure QuorumCommitteeEcho (n : Nat) where
  fromParty : Fin n
  toParty : Fin n
  committeeIdx : Nat
  epoch : UInt64
  binding : Digest256
  mac : Digest256
  deriving DecidableEq, Repr

/-- Verify a `QuorumCommitteeEcho` against expected `(fromParty, toParty, committeeIdx, rec)` using
    `computeQuorumEchoMac` (`quorumEchoMacTag`, `quorum_jorts.rs:989-1000`). -/
def verifyQuorumCommitteeEcho {n : Nat}
    (H : List UInt8 → Digest256)
    (MAC : Digest256 → List UInt8 → Digest256)
    (pairwiseKey : Digest256)
    (expectedFrom expectedTo : Fin n)
    (expectedCIdx : Nat) (expectedRec : BeltLatchRecord)
    (echo : QuorumCommitteeEcho n) : Bool :=
  let bnd := beltRecordBinding H expectedRec
  decide (echo.fromParty = expectedFrom) &&
  decide (echo.toParty = expectedTo) &&
  decide (echo.committeeIdx = expectedCIdx) &&
  decide (echo.epoch = expectedRec.epoch) &&
  decide (echo.binding = bnd) &&
  decide (echo.mac =
    computeQuorumEchoMac MAC pairwiseKey expectedFrom.val expectedTo.val expectedCIdx expectedRec.epoch bnd)

/-- Mask of members `s ∈ Q` supplying a valid `quorumEchoMacTag` echo for `(cIdx, rec)` to `verifier`. -/
def validCommitteeEchoSenders {n : Nat}
    (H : List UInt8 → Digest256)
    (MAC : Digest256 → List UInt8 → Digest256)
    (macKeys : Fin n → Fin n → Digest256)
    (cIdx : Nat) (verifier : Fin n) (Q : CustodiansMask n)
    (rec : BeltLatchRecord) (echoes : List (QuorumCommitteeEcho n)) : CustodiansMask n where
  mem s :=
    Q.mem s &&
      echoes.any (fun e =>
        verifyQuorumCommitteeEcho H MAC (macKeys s verifier) s verifier cIdx rec e)

/-- Verify a `CommitteePermit` (`quorum_jorts.rs:971-1008`): `Q` has index `cIdx` in `chooseMasks n t`,
    `verifier ∈ Q`, `rec.epoch < 2 ^ subtreeHeight`, and at least `echoQuorum` members of `Q`
    supplied valid `quorumEchoMacTag` echoes (`echoQuorum = t` in `QS-A`; `echoQuorum = q` in `QS-B`). -/
def verifyCommitteeEchoPermit {n : Nat}
    (H : List UInt8 → Digest256)
    (MAC : Digest256 → List UInt8 → Digest256)
    (macKeys : Fin n → Fin n → Digest256)
    (t subtreeHeight echoQuorum cIdx : Nat)
    (verifier : Fin n) (Q : CustodiansMask n)
    (rec : BeltLatchRecord) (echoes : List (QuorumCommitteeEcho n)) : Bool :=
  decide (committeeIndexOf t Q = some cIdx) &&
  Q.mem verifier &&
  decide (rec.epoch.toNat < 2 ^ subtreeHeight) &&
  decide (echoQuorum ≤ maskCard (validCommitteeEchoSenders H MAC macKeys cIdx verifier Q rec echoes))

/-- Algebraic certified leaf authorization, not a signature. Actual signature output is
    recorded by `signQuorumWirePermit`. -/
structure ReleasedQuorumLeaf (n : Nat) where
  committee : CustodiansMask n
  committeeIdx : Nat
  localEpoch : UInt64
  globalLeaf : Nat
  verifier : Fin n
  record : BeltLatchRecord
  deriving DecidableEq

/-- Multi-turn distributed `QuorumJorts` network state (`CommitteePartitionedJorts` / `BftShamirJorts`)
    tracking per-`(custodian, committeeIdx)` durable `BeltLatchNodeState` slots, honest persisted logs,
    `quorumEchoMacTag` echoes, and released global-tree leaf records. -/
structure QuorumJortsNetworkState (n : Nat) where
  slots : Fin n → Nat → BeltLatchNodeState
  slotBoundLogs : Fin n → Nat → List BeltLatchRecord
  emittedEchoes : List (QuorumCommitteeEcho n)
  releasedLeaves : List (ReleasedQuorumLeaf n)

/-- Fresh `QuorumJortsNetworkState` with all `(custodian, committeeIdx)` slots at `nextEpoch = 0`. -/
def QuorumJortsNetworkState.init (n subtreeHeight maxWindow : Nat) : QuorumJortsNetworkState n where
  slots := fun _ _ => BeltLatchNodeState.init subtreeHeight maxWindow
  slotBoundLogs := fun _ _ => []
  emittedEchoes := []
  releasedLeaves := []

/-- Open-world multi-turn transitions of `QuorumJortsNetworkState n` across committees, epochs,
    crashes, WAL faults, pairwise `quorumEchoMacTag` broadcasts, and leaf-range releases. -/
inductive QuorumJortsTurn (n : Nat) where
  | bindSlot (p : Fin n) (Q : CustodiansMask n) (rec : BeltLatchRecord)
  | emitSlotEcho (sender receiver : Fin n) (Q : CustodiansMask n)
  | crashAndRecoverSlot (p : Fin n) (Q : CustodiansMask n)
  | armSlotPersistFault (p : Fin n) (Q : CustodiansMask n)
  | corruptSlotDisk (p : Fin n) (Q : CustodiansMask n)
  | releasePartitionedLeaf (verifier : Fin n) (Q : CustodiansMask n)
      (rec : BeltLatchRecord) (echoes : List (QuorumCommitteeEcho n))

/-- Execute one multi-turn `QuorumJortsTurn` step on `QuorumJortsNetworkState n`. -/
def stepQuorumJorts {n : Nat}
    (H : List UInt8 → Digest256)
    (MAC : Digest256 → List UInt8 → Digest256)
    (macKeys : Fin n → Fin n → Digest256)
    (Corrupt : CustodiansMask n)
    (t subtreeHeight echoQuorum : Nat)
    (net : QuorumJortsNetworkState n) (turn : QuorumJortsTurn n) : QuorumJortsNetworkState n :=
  match turn with
  | .bindSlot p Q rec =>
    if Corrupt.mem p || !Q.mem p then net
    else
      match committeeIndexOf t Q with
      | none => net
      | some cIdx =>
        match beltLatchBindStep (net.slots p cIdx) rec with
        | .accepted st' .fresh =>
          { net with
            slots := fun i c => if i = p ∧ c = cIdx then st' else net.slots i c
            slotBoundLogs := fun i c =>
              if i = p ∧ c = cIdx then rec :: net.slotBoundLogs p cIdx else net.slotBoundLogs i c }
        | .accepted st' .replay =>
          { net with slots := fun i c => if i = p ∧ c = cIdx then st' else net.slots i c }
        | .rejected st' _ =>
          { net with slots := fun i c => if i = p ∧ c = cIdx then st' else net.slots i c }
  | .emitSlotEcho sender receiver Q =>
    if Corrupt.mem sender || !Q.mem sender then net
    else
      match committeeIndexOf t Q with
      | none => net
      | some cIdx =>
        let st := net.slots sender cIdx
        if st.walPoisoned then net
        else
          match st.inFlight with
          | none => net
          | some rec =>
            let bnd := beltRecordBinding H rec
            let echo : QuorumCommitteeEcho n :=
              { fromParty := sender
                toParty := receiver
                committeeIdx := cIdx
                epoch := rec.epoch
                binding := bnd
                mac := computeQuorumEchoMac MAC (macKeys sender receiver)
                  sender.val receiver.val cIdx rec.epoch bnd }
            { net with emittedEchoes := echo :: net.emittedEchoes }
  | .crashAndRecoverSlot p Q =>
    if Corrupt.mem p || !Q.mem p then net
    else
      match committeeIndexOf t Q with
      | none => net
      | some cIdx =>
        { net with
          slots := fun i c =>
            if i = p ∧ c = cIdx then beltLatchCrashAndRecover (net.slots p cIdx) else net.slots i c }
  | .armSlotPersistFault p Q =>
    if Corrupt.mem p || !Q.mem p then net
    else
      match committeeIndexOf t Q with
      | none => net
      | some cIdx =>
        let st := net.slots p cIdx
        { net with
          slots := fun i c =>
            if i = p ∧ c = cIdx then { st with failNextPersist := true } else net.slots i c }
  | .corruptSlotDisk p Q =>
    if Corrupt.mem p || !Q.mem p then net
    else
      match committeeIndexOf t Q with
      | none => net
      | some cIdx =>
        let st := net.slots p cIdx
        { net with
          slots := fun i c =>
            if i = p ∧ c = cIdx then
              { st with disk := .corrupted, walPoisoned := true, inFlight := none }
            else net.slots i c }
  | .releasePartitionedLeaf verifier Q rec echoes =>
    if Corrupt.mem verifier then net
    else
      match committeeIndexOf t Q with
      | none => net
      | some cIdx =>
        let st := net.slots verifier cIdx
        if !st.walPoisoned && decide (st.inFlight = some rec) &&
            verifyCommitteeEchoPermit H MAC macKeys t subtreeHeight echoQuorum cIdx verifier Q rec echoes then
          let gLeaf := committeeGlobalLeaf (2 ^ subtreeHeight) cIdx rec.epoch.toNat
          { net with
            releasedLeaves :=
              { committee := Q
                committeeIdx := cIdx
                localEpoch := rec.epoch
                globalLeaf := gLeaf
                verifier := verifier
                record := rec } :: net.releasedLeaves }
        else
          net

/-- Execute an arbitrary multi-turn trace `List (QuorumJortsTurn n)`. -/
def runQuorumJortsTrace {n : Nat}
    (H : List UInt8 → Digest256)
    (MAC : Digest256 → List UInt8 → Digest256)
    (macKeys : Fin n → Fin n → Digest256)
    (Corrupt : CustodiansMask n)
    (t subtreeHeight echoQuorum : Nat)
    (initNet : QuorumJortsNetworkState n) : List (QuorumJortsTurn n) → QuorumJortsNetworkState n
  | [] => initNet
  | turn :: rest =>
    runQuorumJortsTrace H MAC macKeys Corrupt t subtreeHeight echoQuorum
      (stepQuorumJorts H MAC macKeys Corrupt t subtreeHeight echoQuorum initNet turn) rest

theorem runQuorumJortsTrace_append {n : Nat}
    (H : List UInt8 → Digest256)
    (MAC : Digest256 → List UInt8 → Digest256)
    (macKeys : Fin n → Fin n → Digest256)
    (Corrupt : CustodiansMask n)
    (t subtreeHeight echoQuorum : Nat) :
    ∀ (xs ys : List (QuorumJortsTurn n)) (net : QuorumJortsNetworkState n),
      runQuorumJortsTrace H MAC macKeys Corrupt t subtreeHeight echoQuorum net (xs ++ ys) =
      runQuorumJortsTrace H MAC macKeys Corrupt t subtreeHeight echoQuorum
        (runQuorumJortsTrace H MAC macKeys Corrupt t subtreeHeight echoQuorum net xs) ys
  | [], _, _ => rfl
  | x :: xs, ys, net =>
    runQuorumJortsTrace_append H MAC macKeys Corrupt t subtreeHeight echoQuorum xs ys
      (stepQuorumJorts H MAC macKeys Corrupt t subtreeHeight echoQuorum net x)

/-- Pairwise MAC forgery witness on `"QSAG.QUORUM.ECHO.MAC/v1"` (`computeQuorumEchoMac`) for an
    honest `(sender, receiver)` pair. -/
structure QuorumCommitteeEchoMacForgery {n : Nat}
    (MAC : Digest256 → List UInt8 → Digest256)
    (macKeys : Fin n → Fin n → Digest256)
    (Corrupt : CustodiansMask n)
    (emittedEchoes : List (QuorumCommitteeEcho n)) where
  sender : Fin n
  receiver : Fin n
  honest_sender : Corrupt.mem sender = false
  honest_receiver : Corrupt.mem receiver = false
  committeeIdx : Nat
  epoch : UInt64
  forgedBinding : Digest256
  forgedMac : Digest256
  valid_mac : forgedMac =
    computeQuorumEchoMac MAC (macKeys sender receiver) sender.val receiver.val
      committeeIdx epoch forgedBinding
  never_emitted : ∀ e ∈ emittedEchoes,
    ¬ (e.fromParty = sender ∧ e.toParty = receiver ∧ e.committeeIdx = committeeIdx ∧
       e.epoch = epoch ∧ e.binding = forgedBinding)

private def QuorumJortsNetworkInv {n : Nat}
    (H : List UInt8 → Digest256)
    (MAC : Digest256 → List UInt8 → Digest256)
    (macKeys : Fin n → Fin n → Digest256)
    (Corrupt : CustodiansMask n)
    (t subtreeHeight echoQuorum : Nat)
    (net : QuorumJortsNetworkState n) : Prop :=
  (∀ (p : Fin n) (cIdx : Nat), Corrupt.mem p = false →
    HonestNodeWalInv (net.slots p cIdx) (net.slotBoundLogs p cIdx)) ∧
  (∀ e ∈ net.emittedEchoes,
    Corrupt.mem e.fromParty = false ∧
    ∃ r ∈ net.slotBoundLogs e.fromParty e.committeeIdx,
      e.epoch = r.epoch ∧ e.binding = beltRecordBinding H r) ∧
  (∀ rel ∈ net.releasedLeaves,
    Corrupt.mem rel.verifier = false ∧
    committeeIndexOf t rel.committee = some rel.committeeIdx ∧
    rel.localEpoch = rel.record.epoch ∧
    rel.record.epoch.toNat < 2 ^ subtreeHeight ∧
    rel.globalLeaf = committeeGlobalLeaf (2 ^ subtreeHeight) rel.committeeIdx rel.record.epoch.toNat ∧
    ∃ echoes,
      verifyCommitteeEchoPermit H MAC macKeys t subtreeHeight echoQuorum
        rel.committeeIdx rel.verifier rel.committee rel.record echoes = true)

private theorem updateSingleSlot_preserves {n : Nat}
    {slots : Fin n → Nat → BeltLatchNodeState}
    {logs : Fin n → Nat → List BeltLatchRecord}
    {Corrupt : CustodiansMask n}
    (p : Fin n) (cIdx : Nat) (st' : BeltLatchNodeState)
    (hSlots : ∀ (i : Fin n) (c : Nat), Corrupt.mem i = false → HonestNodeWalInv (slots i c) (logs i c))
    (hStep : HonestNodeWalInv st' (logs p cIdx)) :
    ∀ (i : Fin n) (c : Nat), Corrupt.mem i = false →
      HonestNodeWalInv (if i = p ∧ c = cIdx then st' else slots i c) (logs i c) := by
  intro i c hi
  by_cases hic : i = p ∧ c = cIdx
  · rcases hic with ⟨rfl, rfl⟩
    simp only [and_self, ↓reduceIte]
    exact hStep
  · simp only [hic, ↓reduceIte]
    exact hSlots i c hi

private theorem stepQuorumJorts_preserves_inv {n : Nat}
    (H : List UInt8 → Digest256)
    (MAC : Digest256 → List UInt8 → Digest256)
    (macKeys : Fin n → Fin n → Digest256)
    (Corrupt : CustodiansMask n)
    (t subtreeHeight echoQuorum : Nat)
    (net : QuorumJortsNetworkState n) (turn : QuorumJortsTurn n)
    (hInv : QuorumJortsNetworkInv H MAC macKeys Corrupt t subtreeHeight echoQuorum net) :
    QuorumJortsNetworkInv H MAC macKeys Corrupt t subtreeHeight echoQuorum
      (stepQuorumJorts H MAC macKeys Corrupt t subtreeHeight echoQuorum net turn) := by
  rcases hInv with ⟨hSlots, hEchoes, hRels⟩
  cases turn with
  | bindSlot p Q rec =>
    unfold stepQuorumJorts
    if hGuard : (Corrupt.mem p || !Q.mem p) = true then
      simp only [hGuard, ↓reduceIte]; exact ⟨hSlots, hEchoes, hRels⟩
    else
      have hGuardF : (Corrupt.mem p || !Q.mem p) = false := Bool.not_eq_true _ |>.mp hGuard
      have hCpF : Corrupt.mem p = false := (Bool.or_eq_false_iff.mp hGuardF).1
      simp only [hGuardF, Bool.false_eq_true, ↓reduceIte]
      cases hIdx : committeeIndexOf t Q with
      | none => exact ⟨hSlots, hEchoes, hRels⟩
      | some cIdx =>
        dsimp only
        have hStep := honestBind_preserves_walInv (net.slots p cIdx) (net.slotBoundLogs p cIdx) rec (hSlots p cIdx hCpF)
        cases hOut : beltLatchBindStep (net.slots p cIdx) rec with
        | accepted st' out =>
          rw [hOut] at hStep
          cases out with
          | fresh =>
            dsimp only
            refine ⟨?_, ?_, hRels⟩
            · intro i c hi
              by_cases hic : i = p ∧ c = cIdx
              · rcases hic with ⟨rfl, rfl⟩
                simp only [and_self, ↓reduceIte]; exact hStep
              · simp only [hic, ↓reduceIte]; exact hSlots i c hi
            · intro e he
              obtain ⟨hSe, r, hrMem, hrEp, hrBnd⟩ := hEchoes e he
              refine ⟨hSe, r, ?_, hrEp, hrBnd⟩
              by_cases hec : e.fromParty = p ∧ e.committeeIdx = cIdx
              · rcases hec with ⟨hfp, hci⟩
                rw [hfp, hci] at hrMem ⊢
                simp only [and_self, ↓reduceIte, List.mem_cons]
                exact .inr hrMem
              · simp only [hec, ↓reduceIte]; exact hrMem
          | replay =>
            dsimp only at hStep ⊢
            exact ⟨updateSingleSlot_preserves p cIdx st' hSlots hStep, hEchoes, hRels⟩
        | rejected st' _ =>
          rw [hOut] at hStep
          dsimp only at hStep ⊢
          exact ⟨updateSingleSlot_preserves p cIdx st' hSlots hStep, hEchoes, hRels⟩
  | emitSlotEcho sender receiver Q =>
    unfold stepQuorumJorts
    if hGuard : (Corrupt.mem sender || !Q.mem sender) = true then
      simp only [hGuard, ↓reduceIte]; exact ⟨hSlots, hEchoes, hRels⟩
    else
      have hGuardF : (Corrupt.mem sender || !Q.mem sender) = false := Bool.not_eq_true _ |>.mp hGuard
      have hCsF : Corrupt.mem sender = false := (Bool.or_eq_false_iff.mp hGuardF).1
      simp only [hGuardF, Bool.false_eq_true, ↓reduceIte]
      cases hIdx : committeeIndexOf t Q with
      | none => exact ⟨hSlots, hEchoes, hRels⟩
      | some cIdx =>
        dsimp only
        if hPois : (net.slots sender cIdx).walPoisoned = true then
          simp only [hPois, ↓reduceIte]; exact ⟨hSlots, hEchoes, hRels⟩
        else
          have hPoisF : (net.slots sender cIdx).walPoisoned = false := Bool.not_eq_true _ |>.mp hPois
          simp only [hPoisF, Bool.false_eq_true, ↓reduceIte]
          cases hInf : (net.slots sender cIdx).inFlight with
          | none => exact ⟨hSlots, hEchoes, hRels⟩
          | some rec =>
            dsimp only
            have hPay := (hSlots sender cIdx hCsF).2 hPoisF
            have hInLog : rec ∈ net.slotBoundLogs sender cIdx := by
              have h3 := hPay.2.2
              dsimp only at h3
              rw [hInf] at h3
              exact h3.1
            refine ⟨hSlots, ?_, hRels⟩
            intro e he
            rcases List.mem_cons.mp he with rfl | hOld
            · exact ⟨hCsF, rec, hInLog, rfl, rfl⟩
            · exact hEchoes e hOld
  | crashAndRecoverSlot p Q =>
    unfold stepQuorumJorts
    if hGuard : (Corrupt.mem p || !Q.mem p) = true then
      simp only [hGuard, ↓reduceIte]; exact ⟨hSlots, hEchoes, hRels⟩
    else
      have hGuardF : (Corrupt.mem p || !Q.mem p) = false := Bool.not_eq_true _ |>.mp hGuard
      have hCpF : Corrupt.mem p = false := (Bool.or_eq_false_iff.mp hGuardF).1
      simp only [hGuardF, Bool.false_eq_true, ↓reduceIte]
      cases hIdx : committeeIndexOf t Q with
      | none => exact ⟨hSlots, hEchoes, hRels⟩
      | some cIdx =>
        dsimp only
        have hRecovInv : HonestNodeWalInv
            (beltLatchCrashAndRecover (net.slots p cIdx)) (net.slotBoundLogs p cIdx) := by
          rcases hSlots p cIdx hCpF with ⟨hDisk, _⟩
          unfold beltLatchCrashAndRecover
          cases hD : (net.slots p cIdx).disk with
          | unwritten =>
            rw [hD] at hDisk
            change net.slotBoundLogs p cIdx = [] at hDisk
            dsimp only [HonestNodeWalInv, DiskCoversBoundLog, PayloadCoversBoundLog]
            rw [hDisk]
            exact ⟨rfl, fun _ => ⟨fun _ h => False.elim (List.not_mem_nil h),
                                  fun _ h => False.elim (List.not_mem_nil h), trivial⟩⟩
          | persisted pay =>
            rw [hD] at hDisk
            exact ⟨hDisk, fun _ => hDisk⟩
          | corrupted =>
            rw [hD] at hDisk
            exact ⟨hDisk, fun hF => by cases hF⟩
        exact ⟨updateSingleSlot_preserves p cIdx _ hSlots hRecovInv, hEchoes, hRels⟩
  | armSlotPersistFault p Q =>
    unfold stepQuorumJorts
    if hGuard : (Corrupt.mem p || !Q.mem p) = true then
      simp only [hGuard, ↓reduceIte]; exact ⟨hSlots, hEchoes, hRels⟩
    else
      have hGuardF : (Corrupt.mem p || !Q.mem p) = false := Bool.not_eq_true _ |>.mp hGuard
      have hCpF : Corrupt.mem p = false := (Bool.or_eq_false_iff.mp hGuardF).1
      simp only [hGuardF, Bool.false_eq_true, ↓reduceIte]
      cases hIdx : committeeIndexOf t Q with
      | none => exact ⟨hSlots, hEchoes, hRels⟩
      | some cIdx =>
        dsimp only
        exact ⟨updateSingleSlot_preserves p cIdx _ hSlots (hSlots p cIdx hCpF), hEchoes, hRels⟩
  | corruptSlotDisk p Q =>
    unfold stepQuorumJorts
    if hGuard : (Corrupt.mem p || !Q.mem p) = true then
      simp only [hGuard, ↓reduceIte]; exact ⟨hSlots, hEchoes, hRels⟩
    else
      have hGuardF : (Corrupt.mem p || !Q.mem p) = false := Bool.not_eq_true _ |>.mp hGuard
      have hCpF : Corrupt.mem p = false := (Bool.or_eq_false_iff.mp hGuardF).1
      simp only [hGuardF, Bool.false_eq_true, ↓reduceIte]
      cases hIdx : committeeIndexOf t Q with
      | none => exact ⟨hSlots, hEchoes, hRels⟩
      | some cIdx =>
        dsimp only
        have hCorrInv : HonestNodeWalInv
            { net.slots p cIdx with disk := .corrupted, walPoisoned := true, inFlight := none }
            (net.slotBoundLogs p cIdx) := by
          rcases hSlots p cIdx hCpF with ⟨hDisk, _⟩
          exact ⟨diskUniq_of_diskCovers hDisk, fun hF => by cases hF⟩
        exact ⟨updateSingleSlot_preserves p cIdx _ hSlots hCorrInv, hEchoes, hRels⟩
  | releasePartitionedLeaf verifier Q rec echoes =>
    unfold stepQuorumJorts
    if hCv : Corrupt.mem verifier = true then
      simp only [hCv, ↓reduceIte]; exact ⟨hSlots, hEchoes, hRels⟩
    else
      have hCvF : Corrupt.mem verifier = false := Bool.not_eq_true _ |>.mp hCv
      simp only [hCvF, Bool.false_eq_true, ↓reduceIte]
      cases hIdx : committeeIndexOf t Q with
      | none => exact ⟨hSlots, hEchoes, hRels⟩
      | some cIdx =>
        dsimp only
        if hOk : (!((net.slots verifier cIdx).walPoisoned) &&
            decide ((net.slots verifier cIdx).inFlight = some rec) &&
            verifyCommitteeEchoPermit H MAC macKeys t subtreeHeight echoQuorum cIdx verifier Q rec echoes) = true then
          simp only [hOk, ↓reduceIte]
          have hPerm : verifyCommitteeEchoPermit H MAC macKeys t subtreeHeight echoQuorum cIdx verifier Q rec echoes = true :=
            (Bool.and_eq_true_iff.mp hOk).2
          have hEpLt : rec.epoch.toNat < 2 ^ subtreeHeight := by
            unfold verifyCommitteeEchoPermit at hPerm
            rcases Bool.and_eq_true_iff.mp hPerm with ⟨h123, _⟩
            rcases Bool.and_eq_true_iff.mp h123 with ⟨_, hEpDec⟩
            exact of_decide_eq_true hEpDec
          refine ⟨hSlots, hEchoes, ?_⟩
          intro rel hrel
          rcases List.mem_cons.mp hrel with rfl | hOld
          · exact ⟨hCvF, hIdx, rfl, hEpLt, rfl, echoes, hPerm⟩
          · exact hRels rel hOld
        else
          simp only [hOk, Bool.false_eq_true, ↓reduceIte]
          exact ⟨hSlots, hEchoes, hRels⟩

private theorem runQuorumJortsTrace_preserves_inv {n : Nat}
    (H : List UInt8 → Digest256)
    (MAC : Digest256 → List UInt8 → Digest256)
    (macKeys : Fin n → Fin n → Digest256)
    (Corrupt : CustodiansMask n)
    (t subtreeHeight maxWindow echoQuorum : Nat)
    (trace : List (QuorumJortsTurn n)) :
    QuorumJortsNetworkInv H MAC macKeys Corrupt t subtreeHeight echoQuorum
      (runQuorumJortsTrace H MAC macKeys Corrupt t subtreeHeight echoQuorum
        (QuorumJortsNetworkState.init n subtreeHeight maxWindow) trace) := by
  have hInit : QuorumJortsNetworkInv H MAC macKeys Corrupt t subtreeHeight echoQuorum
      (QuorumJortsNetworkState.init n subtreeHeight maxWindow) := by
    refine ⟨?_, ?_, ?_⟩
    · intro p cIdx _
      exact ⟨rfl, fun _ => ⟨fun _ h => False.elim (List.not_mem_nil h),
                            fun _ h => False.elim (List.not_mem_nil h), trivial⟩⟩
    · intro _ h
      exact False.elim (List.not_mem_nil h)
    · intro _ h
      exact False.elim (List.not_mem_nil h)
  generalize QuorumJortsNetworkState.init n subtreeHeight maxWindow = net₀ at hInit
  induction trace generalizing net₀ with
  | nil => exact hInit
  | cons turn rest ih =>
    exact ih _ (stepQuorumJorts_preserves_inv H MAC macKeys Corrupt t subtreeHeight echoQuorum net₀ turn hInit)

private def findMatchingCommitteeEcho {n : Nat}
    (H : List UInt8 → Digest256)
    (MAC : Digest256 → List UInt8 → Digest256)
    (key : Digest256) (s v : Fin n) (cIdx : Nat) (rec : BeltLatchRecord) :
    (echoes : List (QuorumCommitteeEcho n)) →
    echoes.any (fun e => verifyQuorumCommitteeEcho H MAC key s v cIdx rec e) = true →
    { e : QuorumCommitteeEcho n //
      e ∈ echoes ∧ verifyQuorumCommitteeEcho H MAC key s v cIdx rec e = true }
  | [], h => by cases h
  | e :: es, h =>
    if he : verifyQuorumCommitteeEcho H MAC key s v cIdx rec e = true then
      ⟨e, .head es, he⟩
    else
      have hTail : es.any (fun x => verifyQuorumCommitteeEcho H MAC key s v cIdx rec x) = true := by
        simp only [List.any_cons, he, Bool.false_or] at h
        exact h
      let ⟨e', hm', hv'⟩ := findMatchingCommitteeEcho H MAC key s v cIdx rec es hTail
      ⟨e', .tail e hm', hv'⟩

private theorem mask_eq_of_sub_and_card_ge {n : Nat} {A B : CustodiansMask n}
    (hSub : maskSub A B) (hGe : maskCard B ≤ maskCard A) : A = B := by
  have hInterEq : maskInter B A = A := by
    unfold maskInter
    apply congrArg CustodiansMask.mk; funext i
    cases ha : A.mem i
    · exact Bool.and_false _
    · rw [hSub i ha]; rfl
  have hDiffZero : maskCard (maskDiff B A) = 0 := by
    have hSplit := maskCard_diff_add_inter B A
    rw [hInterEq] at hSplit
    omega
  cases A with
  | mk fA =>
    cases B with
    | mk fB =>
      apply congrArg CustodiansMask.mk; funext i
      cases ha : fA i <;> cases hb : fB i
      · rfl
      · exfalso
        have hSubSingle : maskSub ⟨fun j => decide (j = i)⟩ (maskDiff ⟨fB⟩ ⟨fA⟩) := by
          intro j hj
          have hji : j = i := of_decide_eq_true hj
          subst hji; simp [maskDiff, ha, hb]
        have hMono := maskCard_mono hSubSingle
        rw [maskCard_singleton i] at hMono
        omega
      · have hImp := hSub i ha
        dsimp only at hImp
        rw [hb] at hImp
        cases hImp
      · rfl

/-- Readiness predicate on a `(custodian, committeeIdx)` slot to freshly bind `rec`. -/
def SlotReadyForFreshBind (subtreeHeight : Nat) (st : BeltLatchNodeState) (rec : BeltLatchRecord) : Prop :=
  st.height = subtreeHeight ∧
  st.walPoisoned = false ∧
  st.failNextPersist = false ∧
  st.disk ≠ .corrupted ∧
  (∀ cur, st.inFlight = some cur → cur.epoch ≠ rec.epoch) ∧
  st.nextEpoch ≤ rec.epoch.toNat ∧
  rec.epoch.toNat < 2 ^ subtreeHeight ∧
  rec.epoch.toNat ≤ st.nextEpoch + st.maxWindow

theorem slotReadyForFreshBind_init (subtreeHeight maxWindow : Nat) (rec : BeltLatchRecord)
    (hEp0 : rec.epoch = 0) :
    SlotReadyForFreshBind subtreeHeight (BeltLatchNodeState.init subtreeHeight maxWindow) rec := by
  have hPowPos : 0 < 2 ^ subtreeHeight := Nat.two_pow_pos subtreeHeight
  have hEpNat : rec.epoch.toNat = 0 := by rw [hEp0]; rfl
  unfold SlotReadyForFreshBind BeltLatchNodeState.init
  dsimp only
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro h; cases h
  · intro _ h; cases h
  · rw [hEpNat]; exact Nat.le_refl 0
  · rw [hEpNat]; exact hPowPos
  · rw [hEpNat]; exact Nat.zero_le (0 + maxWindow)

private theorem beltLatchBindStep_of_slotReady {subtreeHeight : Nat}
    {st : BeltLatchNodeState} {rec : BeltLatchRecord}
    (hReady : SlotReadyForFreshBind subtreeHeight st rec) :
    beltLatchBindStep st rec =
      .accepted
        { st with
          nextEpoch := rec.epoch.toNat + 1
          inFlight := some rec
          disk := .persisted { nextEpoch := rec.epoch.toNat + 1, inFlight := some rec } }
        .fresh := by
  rcases hReady with ⟨hH, hPois, hFail, hDiskNe, hInfNe, hGe, hLtPow, hLeWin⟩
  unfold beltLatchBindStep
  have hNotLt : ¬ rec.epoch.toNat < st.nextEpoch := Nat.not_lt.mpr hGe
  have hNotExh : ¬ rec.epoch.toNat ≥ 2 ^ st.height := by rw [hH]; exact Nat.not_le.mpr hLtPow
  have hNotJump : ¬ rec.epoch.toNat > st.nextEpoch + st.maxWindow := Nat.not_lt.mpr hLeWin
  have hDiskF : decide (st.disk = .corrupted) = false := decide_eq_false hDiskNe
  simp only [hPois, Bool.false_eq_true, ↓reduceIte]
  cases hInf : st.inFlight with
  | none =>
    simp [hNotLt, hNotExh, hNotJump, hFail, hDiskF]
  | some cur =>
    have hCurNe : decide (cur.epoch = rec.epoch) = false := decide_eq_false (hInfNe cur hInf)
    simp [hCurNe, hNotLt, hNotExh, hNotJump, hFail, hDiskF]

/-- Constructive multi-turn round trace on `QuorumJortsTurn n` executing a complete signing round
    for committee `Q` (at index `cIdx`) coordinated by `verifier` on `rec`:
    1. Every custodian `p ∈ maskMembers Q` durably binds `rec` in slot `cIdx`;
    2. Every custodian `s ∈ maskMembers Q` broadcasts its `quorumEchoMacTag` echo to `verifier`;
    3. `verifier` verifies the full committee echo permit and releases the global-tree leaf record. -/
def buildCommitteeSignTrace {n : Nat}
    (H : List UInt8 → Digest256)
    (MAC : Digest256 → List UInt8 → Digest256)
    (macKeys : Fin n → Fin n → Digest256)
    (cIdx : Nat) (Q : CustodiansMask n) (verifier : Fin n) (rec : BeltLatchRecord) :
    List (QuorumJortsTurn n) :=
  let members := maskMembers Q
  let bindTurns := members.map (fun p => QuorumJortsTurn.bindSlot p Q rec)
  let echoTurns := members.map (fun s => QuorumJortsTurn.emitSlotEcho s verifier Q)
  let bnd := beltRecordBinding H rec
  let echoes : List (QuorumCommitteeEcho n) :=
    members.map (fun s =>
      { fromParty := s
        toParty := verifier
        committeeIdx := cIdx
        epoch := rec.epoch
        binding := bnd
        mac := computeQuorumEchoMac MAC (macKeys s verifier) s.val verifier.val cIdx rec.epoch bnd })
  bindTurns ++ echoTurns ++ [.releasePartitionedLeaf verifier Q rec echoes]

private theorem runBindTurns_slots {n : Nat}
    (H : List UInt8 → Digest256)
    (MAC : Digest256 → List UInt8 → Digest256)
    (macKeys : Fin n → Fin n → Digest256)
    (Corrupt : CustodiansMask n)
    (t subtreeHeight echoQuorum cIdx : Nat)
    (Q : CustodiansMask n) (rec : BeltLatchRecord)
    (hIdx : committeeIndexOf t Q = some cIdx) :
    ∀ (ms : List (Fin n)) (net : QuorumJortsNetworkState n),
      ms.Nodup →
      (∀ p ∈ ms, Corrupt.mem p = false ∧ Q.mem p = true ∧
        SlotReadyForFreshBind subtreeHeight (net.slots p cIdx) rec) →
      let net' := runQuorumJortsTrace H MAC macKeys Corrupt t subtreeHeight echoQuorum net
        (ms.map (fun p => QuorumJortsTurn.bindSlot p Q rec))
      (∀ p ∈ ms,
        (net'.slots p cIdx).walPoisoned = false ∧
        (net'.slots p cIdx).inFlight = some rec ∧
        (net'.slots p cIdx).nextEpoch = rec.epoch.toNat + 1) ∧
      (∀ q, q ∉ ms → net'.slots q cIdx = net.slots q cIdx) := by
  intro ms
  induction ms with
  | nil =>
    intro net _ _
    exact ⟨fun _ h => False.elim (List.not_mem_nil h), fun _ _ => rfl⟩
  | cons m ms ih =>
    intro net hNd hReadyAll
    dsimp only [List.map, runQuorumJortsTrace]
    obtain ⟨hmNotIn, hNdTail⟩ := List.nodup_cons.mp hNd
    obtain ⟨hmHon, hmInQ, hmReady⟩ := hReadyAll m (.head ms)
    have hBindM := beltLatchBindStep_of_slotReady hmReady
    let netMid := stepQuorumJorts H MAC macKeys Corrupt t subtreeHeight echoQuorum net (.bindSlot m Q rec)
    have hNetMidSlots : ∀ (i : Fin n) (c : Nat),
        netMid.slots i c =
          if i = m ∧ c = cIdx then
            { net.slots m cIdx with
              nextEpoch := rec.epoch.toNat + 1
              inFlight := some rec
              disk := .persisted { nextEpoch := rec.epoch.toNat + 1, inFlight := some rec } }
          else net.slots i c := by
      intro i c
      dsimp only [netMid, stepQuorumJorts]
      simp only [hmHon, hmInQ, Bool.not_true, Bool.or_self, Bool.false_eq_true, ↓reduceIte, hIdx, hBindM]
    have hReadyTail : ∀ p ∈ ms, Corrupt.mem p = false ∧ Q.mem p = true ∧
        SlotReadyForFreshBind subtreeHeight (netMid.slots p cIdx) rec := by
      intro p hp
      obtain ⟨hpHon, hpQ, hpReady⟩ := hReadyAll p (.tail m hp)
      have hNe : p ≠ m := fun he => hmNotIn (he ▸ hp)
      rw [hNetMidSlots p cIdx]
      simp only [hNe, false_and, ↓reduceIte]
      exact ⟨hpHon, hpQ, hpReady⟩
    obtain ⟨ihMem, ihOut⟩ := ih netMid hNdTail hReadyTail
    refine ⟨?_, ?_⟩
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hpTail
      · have hUnch :
            (runQuorumJortsTrace H MAC macKeys Corrupt t subtreeHeight echoQuorum netMid
              (ms.map (fun p => QuorumJortsTurn.bindSlot p Q rec))).slots p cIdx =
            netMid.slots p cIdx := ihOut p hmNotIn
        rw [hUnch, hNetMidSlots p cIdx]
        simp [hmReady.2.1]
      · exact ihMem p hpTail
    · intro q hqNot
      have hqNeM : q ≠ m := fun he => hqNot (he ▸ .head ms)
      have hqNotTail : q ∉ ms := fun hm => hqNot (.tail m hm)
      have hUnch :
          (runQuorumJortsTrace H MAC macKeys Corrupt t subtreeHeight echoQuorum netMid
            (ms.map (fun p => QuorumJortsTurn.bindSlot p Q rec))).slots q cIdx =
          netMid.slots q cIdx := ihOut q hqNotTail
      rw [hUnch, hNetMidSlots q cIdx]
      simp [hqNeM]

private theorem runEchoTurns_emits {n : Nat}
    (H : List UInt8 → Digest256)
    (MAC : Digest256 → List UInt8 → Digest256)
    (macKeys : Fin n → Fin n → Digest256)
    (Corrupt : CustodiansMask n)
    (t subtreeHeight echoQuorum cIdx : Nat)
    (Q : CustodiansMask n) (verifier : Fin n) (rec : BeltLatchRecord)
    (hIdx : committeeIndexOf t Q = some cIdx) :
    ∀ (ms : List (Fin n)) (net : QuorumJortsNetworkState n),
      (∀ s ∈ ms, Corrupt.mem s = false ∧ Q.mem s = true ∧
        (net.slots s cIdx).walPoisoned = false ∧ (net.slots s cIdx).inFlight = some rec) →
      let net' := runQuorumJortsTrace H MAC macKeys Corrupt t subtreeHeight echoQuorum net
        (ms.map (fun s => QuorumJortsTurn.emitSlotEcho s verifier Q))
      net'.slots = net.slots ∧
      (∀ e ∈ net.emittedEchoes, e ∈ net'.emittedEchoes) ∧
      (∀ s ∈ ms,
        ({ fromParty := s
           toParty := verifier
           committeeIdx := cIdx
           epoch := rec.epoch
           binding := beltRecordBinding H rec
           mac := computeQuorumEchoMac MAC (macKeys s verifier) s.val verifier.val
             cIdx rec.epoch (beltRecordBinding H rec) } : QuorumCommitteeEcho n) ∈ net'.emittedEchoes)
  | [], net, _ => ⟨rfl, fun _ h => h, fun _ h => by cases h⟩
  | s :: ms, net, hAll => by
    obtain ⟨hsHon, hsQ, hsPois, hsInf⟩ := hAll s (.head ms)
    let netMid := stepQuorumJorts H MAC macKeys Corrupt t subtreeHeight echoQuorum net (.emitSlotEcho s verifier Q)
    have hMidEq : netMid =
        { net with
          emittedEchoes :=
            { fromParty := s
              toParty := verifier
              committeeIdx := cIdx
              epoch := rec.epoch
              binding := beltRecordBinding H rec
              mac := computeQuorumEchoMac MAC (macKeys s verifier) s.val verifier.val
                cIdx rec.epoch (beltRecordBinding H rec) } :: net.emittedEchoes } := by
      dsimp only [netMid, stepQuorumJorts]
      simp [hsHon, hsQ, hIdx, hsPois, hsInf]
    have hTail : ∀ x ∈ ms, Corrupt.mem x = false ∧ Q.mem x = true ∧
        (netMid.slots x cIdx).walPoisoned = false ∧ (netMid.slots x cIdx).inFlight = some rec := by
      intro x hx
      rw [hMidEq]
      exact hAll x (.tail s hx)
    obtain ⟨ihSlots, ihSub, ihMem⟩ :=
      runEchoTurns_emits H MAC macKeys Corrupt t subtreeHeight echoQuorum cIdx Q verifier rec hIdx
        ms netMid hTail
    refine ⟨ihSlots.trans (by rw [hMidEq]), ?_, ?_⟩
    · intro e he
      apply ihSub
      rw [hMidEq]
      exact .tail _ he
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hxTail
      · apply ihSub
        rw [hMidEq]
        exact .head _
      · exact ihMem x hxTail

/-- **Crown Jewel 2 — Multi-Turn Committee-Partitioned & BFT Quorum-Switching `Jorts` Theorem
    (`committee_partitioned_jorts_safe_and_live_for_2f_plus_1`)**:
    Over an arbitrary open-world multi-turn execution `trace : List (QuorumJortsTurn n)` starting
    from `QuorumJortsNetworkState.init n subtreeHeight maxWindow`:
    1. **(a) Multi-Turn Global Leaf Non-Equivocation & Subtree Cursor Monotonicity**:
       Whenever `(echoQuorum = t ∧ f < t)` (Mode `QS-A` committee-partitioned subtrees across
       `chooseMasks n t`, including `n = 2 * f + 1, t = f + 1`: `(2, 3, 1)` = 3 subtrees and
       `(3, 5, 2)` = 10 subtrees) OR `2 * echoQuorum > n + f` (Mode `QS-B` global BFT quorum):
       - Any two released leaf signatures `rel₁, rel₂ ∈ net.releasedLeaves` across the entire
         multi-turn `trace` that target the same global Merkle leaf (`rel₁.globalLeaf = rel₂.globalLeaf`)
         necessarily agree on `(committeeIdx, committee, localEpoch)` AND satisfy
         `rel₁.record = rel₂.record` unless the adversary produced an explicit
         `QuorumCommitteeEchoMacForgery` (`"QSAG.QUORUM.ECHO.MAC/v1"`) or `HashCollision256 H`
         (`"QSAG.BELT.LATCH.BINDING/v1"`)!
       - Every honest unpoisoned slot `(p, cIdx)` maintains a monotone `nextEpoch` cursor strictly
         above all bound epochs in `net.slotBoundLogs p cIdx` across arbitrary crashes and replays.
    2. **(b) Intra-Committee `(t - 1)`-Corruption & Cross-Committee (`Q' ≠ Q`) Share Privacy**:
       When `f < t`, every `t`-committee `Q` constructively yields an honest member `pHon ∈ Q \ Corrupt`
       and an involutive `SimpleEquiv` hiding `Q`'s `t`-of-`t` leaf secrets from `Corrupt`, AND for
       every other `t`-committee `Q' ≠ Q`, `Q'`'s share view has **exact `0` statistical distance**
       (`finSum`) between any two leaf secrets `sec₁, sec₂`.
    3. **(c) Multi-Turn Live Signing via `selectSubcommittee` under `≤ f` Faults (`n = 2 * f + 1`)**:
       Whenever `0 < t`, `echoQuorum ≤ t`, and `Online` has `t ≤ maskCard (maskDiff Online Corrupt)`,
       `live := selectSubcommittee t (maskDiff Online Corrupt) hOnlineHon` selects an all-honest
       online committee `live.1 ∈ chooseMasks n t`; from ANY state `net` whose `live.1` slots at
       `cIdx` satisfy `SlotReadyForFreshBind subtreeHeight _ rec`, appending the multi-turn trace
       `buildCommitteeSignTrace` advances `(slots p cIdx).nextEpoch` to `rec.epoch.toNat + 1` across
       `live.1`, emits genuine `quorumEchoMacTag` echoes, appends the certified `ReleasedQuorumLeaf`
       at `committeeGlobalLeaf (2 ^ subtreeHeight) cIdx rec.epoch.toNat`, and reconstructs
       `xorFin256 t (dealAdditiveShares t secret tape) = secret`! -/
theorem committee_partitioned_jorts_safe_and_live_for_2f_plus_1
    {n t f subtreeHeight maxWindow echoQuorum : Nat}
    (H : List UInt8 → Digest256)
    (MAC : Digest256 → List UInt8 → Digest256)
    (macKeys : Fin n → Fin n → Digest256)
    (Corrupt : CustodiansMask n) (hCorrupt : maskCard Corrupt ≤ f) :
    -- (a) Multi-turn global leaf non-equivocation & cursor monotonicity across arbitrary List (QuorumJortsTurn n):
    (((echoQuorum = t ∧ f < t) ∨ 2 * echoQuorum > n + f) →
      ∀ (trace : List (QuorumJortsTurn n)),
        let net := runQuorumJortsTrace H MAC macKeys Corrupt t subtreeHeight echoQuorum
          (QuorumJortsNetworkState.init n subtreeHeight maxWindow) trace
        (∀ rel₁ ∈ net.releasedLeaves, ∀ rel₂ ∈ net.releasedLeaves,
          rel₁.globalLeaf = rel₂.globalLeaf →
          rel₁.committeeIdx = rel₂.committeeIdx ∧
          rel₁.committee = rel₂.committee ∧
          rel₁.localEpoch = rel₂.localEpoch ∧
          (rel₁.record = rel₂.record ∨
           Nonempty (QuorumCommitteeEchoMacForgery MAC macKeys Corrupt net.emittedEchoes) ∨
           Nonempty (HashCollision256 H))) ∧
        (∀ (p : Fin n) (cIdx : Nat),
          Corrupt.mem p = false →
          (net.slots p cIdx).walPoisoned = false →
          ∀ r ∈ net.slotBoundLogs p cIdx, r.epoch.toNat < (net.slots p cIdx).nextEpoch)) ∧
    -- (b) Intra-committee Corrupt share hiding (when f < t) and cross-committee Q' ≠ Q 0-distance share independence:
    ((f < t →
      ∀ (Q : CustodiansMask n), maskCard Q = t → ∀ (sec₁ sec₂ : Digest256),
        ∃ (pHon : Fin n) (bijCorr : SimpleEquiv (Fin (t - 1) → Digest256) (Fin (t - 1) → Digest256)),
          Q.mem pHon = true ∧
          Corrupt.mem pHon = false ∧
          (∀ tape : Fin (t - 1) → Digest256,
            committeeViewerObservation t Q Corrupt sec₂ (bijCorr.toFun tape) =
              committeeViewerObservation t Q Corrupt sec₁ tape)) ∧
     (∀ (Q Q' : CustodiansMask n), maskCard Q = t → maskCard Q' = t →
        Q' ≠ Q →
        ∀ (sec₁ sec₂ : Digest256),
          ∃ (pMiss : Fin n) (bijCross : SimpleEquiv (Fin (t - 1) → Digest256) (Fin (t - 1) → Digest256)),
            Q.mem pMiss = true ∧ Q'.mem pMiss = false ∧
            (∀ tape : Fin (t - 1) → Digest256,
              committeeViewerObservation t Q Q' sec₂ (bijCross.toFun tape) =
                committeeViewerObservation t Q Q' sec₁ tape) ∧
            (∀ (Card : Nat) (enum : SimpleEquiv (Fin Card) (Fin (t - 1) → Digest256))
               (D : (Fin n → Option Digest256) → Bool),
              finSum Card (fun r => if D (committeeViewerObservation t Q Q' sec₁ (enum.toFun r)) then 1 else 0) =
                finSum Card (fun r => if D (committeeViewerObservation t Q Q' sec₂ (enum.toFun r)) then 1 else 0)))) ∧
    -- (c) Multi-turn live committee selection & signing round progression on QuorumJortsNetworkState:
    (0 < t → echoQuorum ≤ t →
      ∀ (Online : CustodiansMask n) (hOnlineHon : t ≤ maskCard (maskDiff Online Corrupt)),
        let live := selectSubcommittee t (maskDiff Online Corrupt) hOnlineHon
        live.1 ∈ chooseMasks n t ∧
        maskCard live.1 = t ∧
        (∀ p : Fin n, live.1.mem p = true → Online.mem p = true ∧ Corrupt.mem p = false) ∧
        (∀ (secret : Digest256) (tape : Fin (t - 1) → Digest256),
          xorFin256 t (dealAdditiveShares t secret tape) = secret) ∧
        (∀ (cIdx : Nat) (verifier : Fin n) (rec : BeltLatchRecord) (net : QuorumJortsNetworkState n),
          committeeIndexOf t live.1 = some cIdx →
          live.1.mem verifier = true →
          (∀ p : Fin n, live.1.mem p = true → SlotReadyForFreshBind subtreeHeight (net.slots p cIdx) rec) →
          let net' := runQuorumJortsTrace H MAC macKeys Corrupt t subtreeHeight echoQuorum net
            (buildCommitteeSignTrace H MAC macKeys cIdx live.1 verifier rec)
          (∀ p : Fin n, live.1.mem p = true → (net'.slots p cIdx).nextEpoch = rec.epoch.toNat + 1) ∧
          ({ committee := live.1
             committeeIdx := cIdx
             localEpoch := rec.epoch
             globalLeaf := committeeGlobalLeaf (2 ^ subtreeHeight) cIdx rec.epoch.toNat
             verifier := verifier
             record := rec } : ReleasedQuorumLeaf n) ∈ net'.releasedLeaves)) := by
  have hBuildBij : ∀ (Q Viewer : CustodiansMask n) (hQ : maskCard Q = t)
      (pMiss : Fin n) (hpInQ : Q.mem pMiss = true) (hpNotV : Viewer.mem pMiss = false)
      (sec₁ sec₂ : Digest256),
      ∃ bij : SimpleEquiv (Fin (t - 1) → Digest256) (Fin (t - 1) → Digest256),
        ∀ tape : Fin (t - 1) → Digest256,
          committeeViewerObservation t Q Viewer sec₂ (bij.toFun tape) =
            committeeViewerObservation t Q Viewer sec₁ tape := by
    intro Q Viewer hQ pMiss hpInQ hpNotV sec₁ sec₂
    have hpMemList : pMiss ∈ maskMembers Q := (mem_maskMembers_iff Q pMiss).mpr hpInQ
    obtain ⟨missIdx, hMissPos⟩ := memberPositionAux_some_of_mem pMiss (maskMembers Q) hpMemList
    have hMissLt : missIdx < t := by
      have h1 := memberPositionAux_lt pMiss (maskMembers Q) hMissPos
      rw [maskMembers_length Q, hQ] at h1
      exact h1
    let missingSlot : Fin t := ⟨missIdx, hMissLt⟩
    refine ⟨committeeAdditiveRebalanceEquiv t missingSlot sec₁ sec₂, ?_⟩
    intro tape
    funext p
    unfold committeeViewerObservation
    cases hVp : Viewer.mem p
    · rfl
    · simp only [↓reduceIte]
      unfold committeeCustodianShare
      cases hPosP : memberPositionAux p (maskMembers Q) with
      | none => rfl
      | some idxP =>
        dsimp only
        by_cases hLtP : idxP < t
        · simp only [hLtP, ↓reduceDIte]
          have hSlotNe : (⟨idxP, hLtP⟩ : Fin t) ≠ missingSlot := by
            intro hSlotEq
            have hIdxEq : idxP = missIdx := congrArg Fin.val hSlotEq
            subst hIdxEq
            have hpEq : p = pMiss := memberPositionAux_inj (maskMembers Q) hPosP hMissPos
            subst hpEq
            rw [hpNotV] at hVp
            cases hVp
          exact congrArg some
            (dealAdditiveShares_rebalance_other t missingSlot ⟨idxP, hLtP⟩ hSlotNe sec₁ sec₂ tape)
        · simp only [hLtP, ↓reduceDIte]
  refine ⟨?_, ⟨?_, ?_⟩, ?_⟩
  · -- Part (a): Multi-turn non-equivocation & cursor monotonicity
    intro hSafeRegime trace net
    have hNetInv :=
      runQuorumJortsTrace_preserves_inv H MAC macKeys Corrupt t subtreeHeight maxWindow echoQuorum trace
    rcases hNetInv with ⟨hSlotInvs, hEchoInvs, hRelInvs⟩
    refine ⟨?_, ?_⟩
    · intro rel₁ hRel₁ rel₂ hRel₂ hSameGLeaf
      obtain ⟨hv₁Hon, hIdx₁, hLoc₁, hLt₁, hGL₁, echoes₁, hPerm₁⟩ := hRelInvs rel₁ hRel₁
      obtain ⟨hv₂Hon, hIdx₂, hLoc₂, hLt₂, hGL₂, echoes₂, hPerm₂⟩ := hRelInvs rel₂ hRel₂
      have hDisj :=
        committee_leaf_ranges_disjoint hLt₁ hLt₂ (hGL₁.symm.trans (hSameGLeaf.trans hGL₂))
      have hCIdxEq : rel₁.committeeIdx = rel₂.committeeIdx := hDisj.1
      have hRecEpEq : rel₁.record.epoch = rel₂.record.epoch :=
        UInt64.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq hDisj.2)
      have hCommEq : rel₁.committee = rel₂.committee :=
        committeeIndexOf_inj hIdx₁ (hCIdxEq ▸ hIdx₂)
      have hLocEpEq : rel₁.localEpoch = rel₂.localEpoch :=
        hLoc₁.trans (hRecEpEq.trans hLoc₂.symm)
      refine ⟨hCIdxEq, hCommEq, hLocEpEq, ?_⟩
      let cIdx := rel₁.committeeIdx
      let Q := rel₁.committee
      have hQCard : maskCard Q = t := committeeIndexOf_card hIdx₁
      let S₁ := validCommitteeEchoSenders H MAC macKeys cIdx rel₁.verifier Q rel₁.record echoes₁
      let S₂ := validCommitteeEchoSenders H MAC macKeys cIdx rel₂.verifier Q rel₂.record echoes₂
      have hCardS₁ : echoQuorum ≤ maskCard S₁ := by
        unfold verifyCommitteeEchoPermit at hPerm₁
        exact of_decide_eq_true (Bool.and_eq_true_iff.mp hPerm₁).2
      have hCardS₂ : echoQuorum ≤ maskCard S₂ := by
        unfold verifyCommitteeEchoPermit at hPerm₂
        have hP2 := (Bool.and_eq_true_iff.mp hPerm₂).2
        rw [← hCIdxEq, ← hCommEq] at hP2
        exact of_decide_eq_true hP2
      have hSubS₁ : maskSub S₁ Q := fun s hs => (Bool.and_eq_true_iff.mp hs).1
      have hSubS₂ : maskSub S₂ Q := fun s hs => (Bool.and_eq_true_iff.mp hs).1
      have hHonInterPos : 0 < maskCard (maskDiff (maskInter S₁ S₂) Corrupt) := by
        rcases hSafeRegime with ⟨rfl, hFltT⟩ | hBftQuorum
        · have hS1EqQ : S₁ = Q := mask_eq_of_sub_and_card_ge hSubS₁ (hQCard ▸ hCardS₁)
          have hS2EqQ : S₂ = Q := mask_eq_of_sub_and_card_ge hSubS₂ (hQCard ▸ hCardS₂)
          have hInterQ : maskInter S₁ S₂ = Q := by
            rw [hS1EqQ, hS2EqQ]
            apply congrArg CustodiansMask.mk; funext s; exact Bool.and_self _
          rw [hInterQ]
          have hDiff := maskCard_diff_ge Q Corrupt
          omega
        · have hIE := maskCard_inter_add_n_ge S₁ S₂
          have hDiff := maskCard_diff_ge (maskInter S₁ S₂) Corrupt
          omega
      let ⟨pHon, hpHon⟩ := extractMaskMember (maskDiff (maskInter S₁ S₂) Corrupt) hHonInterPos
      simp only [maskDiff, maskInter, Bool.and_eq_true, Bool.not_eq_true'] at hpHon
      obtain ⟨⟨hpS₁, hpS₂⟩, hpNotCorr⟩ := hpHon
      have hAny₁ : echoes₁.any
          (fun e => verifyQuorumCommitteeEcho H MAC (macKeys pHon rel₁.verifier)
            pHon rel₁.verifier cIdx rel₁.record e) = true :=
        (Bool.and_eq_true_iff.mp hpS₁).2
      have hAny₂ : echoes₂.any
          (fun e => verifyQuorumCommitteeEcho H MAC (macKeys pHon rel₂.verifier)
            pHon rel₂.verifier cIdx rel₂.record e) = true :=
        (Bool.and_eq_true_iff.mp hpS₂).2
      let ⟨e₁, _, hVer₁⟩ :=
        findMatchingCommitteeEcho H MAC (macKeys pHon rel₁.verifier) pHon rel₁.verifier cIdx rel₁.record echoes₁ hAny₁
      let ⟨e₂, _, hVer₂⟩ :=
        findMatchingCommitteeEcho H MAC (macKeys pHon rel₂.verifier) pHon rel₂.verifier cIdx rel₂.record echoes₂ hAny₂
      unfold verifyQuorumCommitteeEcho at hVer₁ hVer₂
      rcases Bool.and_eq_true_iff.mp hVer₁ with ⟨_, hMac₁⟩
      rcases Bool.and_eq_true_iff.mp hVer₂ with ⟨_, hMac₂⟩
      let bnd₁ := beltRecordBinding H rel₁.record
      let bnd₂ := beltRecordBinding H rel₂.record
      if hEm₁ : net.emittedEchoes.any
          (fun e => decide (e.fromParty = pHon) && decide (e.toParty = rel₁.verifier) &&
            decide (e.committeeIdx = cIdx) && decide (e.epoch = rel₁.record.epoch) &&
            decide (e.binding = bnd₁)) = true then
        if hEm₂ : net.emittedEchoes.any
            (fun e => decide (e.fromParty = pHon) && decide (e.toParty = rel₂.verifier) &&
              decide (e.committeeIdx = cIdx) && decide (e.epoch = rel₂.record.epoch) &&
              decide (e.binding = bnd₂)) = true then
          obtain ⟨eh₁, hMemEh₁, hPred₁⟩ := List.any_eq_true.mp hEm₁
          obtain ⟨eh₂, hMemEh₂, hPred₂⟩ := List.any_eq_true.mp hEm₂
          rcases Bool.and_eq_true_iff.mp hPred₁ with ⟨hP1a, hB1⟩
          rcases Bool.and_eq_true_iff.mp hP1a with ⟨hP1b, hE1⟩
          rcases Bool.and_eq_true_iff.mp hP1b with ⟨hP1c, hC1⟩
          rcases Bool.and_eq_true_iff.mp hP1c with ⟨hF1, _⟩
          rcases Bool.and_eq_true_iff.mp hPred₂ with ⟨hP2a, hB2⟩
          rcases Bool.and_eq_true_iff.mp hP2a with ⟨hP2b, hE2⟩
          rcases Bool.and_eq_true_iff.mp hP2b with ⟨hP2c, hC2⟩
          rcases Bool.and_eq_true_iff.mp hP2c with ⟨hF2, _⟩
          obtain ⟨_, r₁', hr₁Mem, hr₁Ep, hr₁Bnd⟩ := hEchoInvs eh₁ hMemEh₁
          obtain ⟨_, r₂', hr₂Mem, hr₂Ep, hr₂Bnd⟩ := hEchoInvs eh₂ hMemEh₂
          rw [of_decide_eq_true hF1, of_decide_eq_true hC1] at hr₁Mem
          rw [of_decide_eq_true hF2, of_decide_eq_true hC2] at hr₂Mem
          have hR1R2Ep : r₁'.epoch = r₂'.epoch := by
            have he1 : r₁'.epoch = rel₁.record.epoch := hr₁Ep.symm.trans (of_decide_eq_true hE1)
            have he2 : r₂'.epoch = rel₂.record.epoch := hr₂Ep.symm.trans (of_decide_eq_true hE2)
            exact he1.trans (hRecEpEq.trans he2.symm)
          have hR1EqR2 : r₁' = r₂' :=
            diskUniq_of_diskCovers (hSlotInvs pHon cIdx hpNotCorr).1 r₁' hr₁Mem r₂' hr₂Mem hR1R2Ep
          have hBndEq : bnd₁ = bnd₂ := by
            have hb1 : bnd₁ = beltRecordBinding H r₁' := (of_decide_eq_true hB1).symm.trans hr₁Bnd
            have hb2 : bnd₂ = beltRecordBinding H r₂' := (of_decide_eq_true hB2).symm.trans hr₂Bnd
            rw [hb1, hb2, hR1EqR2]
          rcases beltRecordBinding_binding H hBndEq with hRecEq | hColl
          · exact .inl hRecEq
          · exact .inr (.inr hColl)
        else
          refine .inr (.inl ⟨{
            sender := pHon
            receiver := rel₂.verifier
            honest_sender := hpNotCorr
            honest_receiver := hv₂Hon
            committeeIdx := cIdx
            epoch := rel₂.record.epoch
            forgedBinding := bnd₂
            forgedMac := e₂.mac
            valid_mac := of_decide_eq_true hMac₂
            never_emitted := ?_ }⟩)
          intro e he ⟨hf, ht, hc, hep, hb⟩
          apply hEm₂
          exact List.any_eq_true.mpr ⟨e, he, by simp [hf, ht, hc, hep, hb]⟩
      else
        refine .inr (.inl ⟨{
          sender := pHon
          receiver := rel₁.verifier
          honest_sender := hpNotCorr
          honest_receiver := hv₁Hon
          committeeIdx := cIdx
          epoch := rel₁.record.epoch
          forgedBinding := bnd₁
          forgedMac := e₁.mac
          valid_mac := of_decide_eq_true hMac₁
          never_emitted := ?_ }⟩)
        intro e he ⟨hf, ht, hc, hep, hb⟩
        apply hEm₁
        exact List.any_eq_true.mpr ⟨e, he, by simp [hf, ht, hc, hep, hb]⟩
    · intro p cIdx hpHon hUnpois r hrMem
      exact ((hSlotInvs p cIdx hpHon).2 hUnpois).2.1 r hrMem
  · -- Part (b.1): Intra-committee Corrupt share hiding
    intro hFltT Q hQ sec₁ sec₂
    have hDiffPos : 0 < maskCard (maskDiff Q Corrupt) := by
      have hGe := maskCard_diff_ge Q Corrupt
      omega
    let ⟨pHon, hpHon⟩ := extractMaskMember (maskDiff Q Corrupt) hDiffPos
    simp only [maskDiff, Bool.and_eq_true, Bool.not_eq_true'] at hpHon
    obtain ⟨bijCorr, hViewEq⟩ := hBuildBij Q Corrupt hQ pHon hpHon.1 hpHon.2 sec₁ sec₂
    exact ⟨pHon, bijCorr, hpHon.1, hpHon.2, hViewEq⟩
  · -- Part (b.2): Cross-committee Q' ≠ Q 0-distance share independence
    intro Q Q' hQ hQ' hNe sec₁ sec₂
    have hDiffPos : 0 < maskCard (maskDiff Q Q') := by
      if hZero : maskCard (maskDiff Q Q') = 0 then
        exfalso
        apply hNe
        have hInterEq : maskCard (maskInter Q Q') = t := by
          have hSplit := maskCard_diff_add_inter Q Q'
          omega
        have hDiff2Zero : maskCard (maskDiff Q' Q) = 0 := by
          have hSplit2 := maskCard_diff_add_inter Q' Q
          have hSymm : maskInter Q' Q = maskInter Q Q' := by
            apply congrArg CustodiansMask.mk; funext i; exact Bool.and_comm _ _
          rw [hSymm] at hSplit2
          omega
        cases Q with
        | mk fQ =>
          cases Q' with
          | mk fQ' =>
            apply congrArg CustodiansMask.mk
            funext i
            cases h1 : fQ i <;> cases h2 : fQ' i
            · rfl
            · exfalso
              have hSubSingle : maskSub ⟨fun j => decide (j = i)⟩ (maskDiff ⟨fQ'⟩ ⟨fQ⟩) := by
                intro j hj
                have hji : j = i := of_decide_eq_true hj
                subst hji; simp [maskDiff, h1, h2]
              have hMono := maskCard_mono hSubSingle
              rw [maskCard_singleton i] at hMono
              omega
            · exfalso
              have hSubSingle : maskSub ⟨fun j => decide (j = i)⟩ (maskDiff ⟨fQ⟩ ⟨fQ'⟩) := by
                intro j hj
                have hji : j = i := of_decide_eq_true hj
                subst hji; simp [maskDiff, h1, h2]
              have hMono := maskCard_mono hSubSingle
              rw [maskCard_singleton i] at hMono
              omega
            · rfl
      else
        omega
    let ⟨pMiss, hpMiss⟩ := extractMaskMember (maskDiff Q Q') hDiffPos
    simp only [maskDiff, Bool.and_eq_true, Bool.not_eq_true'] at hpMiss
    obtain ⟨bijCross, hViewEq⟩ := hBuildBij Q Q' hQ pMiss hpMiss.1 hpMiss.2 sec₁ sec₂
    refine ⟨pMiss, bijCross, hpMiss.1, hpMiss.2, hViewEq, ?_⟩
    intro Card enum D
    let finBij : SimpleEquiv (Fin Card) (Fin Card) :=
      { toFun := fun r => enum.invFun (bijCross.toFun (enum.toFun r))
        invFun := fun r => enum.invFun (bijCross.invFun (enum.toFun r))
        left_inv := fun r => by rw [enum.right_inv, bijCross.left_inv, enum.left_inv]
        right_inv := fun r => by rw [enum.right_inv, bijCross.right_inv, enum.left_inv] }
    have hPerm := finSum_comp_simpleEquiv Card finBij
      (fun r => if D (committeeViewerObservation t Q Q' sec₂ (enum.toFun r)) then 1 else 0)
    rw [← hPerm]
    apply finSum_congr
    intro r
    dsimp only [finBij]
    rw [enum.right_inv, hViewEq (enum.toFun r)]
  · -- Part (c): Multi-turn live committee selection & signing round progression
    intro hTPos hEqLeT Online hOnlineHon live
    have hMemChoose : live.1 ∈ chooseMasks n t := by
      have h := mem_chooseMasks_of_card n live.1
      rw [live.2.1] at h
      exact h
    have hHonMem : ∀ p : Fin n, live.1.mem p = true → Online.mem p = true ∧ Corrupt.mem p = false := by
      intro p hp
      have hSub := live.2.2 p hp
      simp only [maskDiff, Bool.and_eq_true, Bool.not_eq_true'] at hSub
      exact hSub
    refine ⟨hMemChoose, live.2.1, hHonMem,
            fun secret tape => reconstruct_dealAdditiveShares t hTPos secret tape, ?_⟩
    intro cIdx verifier rec net hIdx hvInLive hSlotsReady
    unfold buildCommitteeSignTrace
    dsimp only
    rw [runQuorumJortsTrace_append, runQuorumJortsTrace_append]
    let members := maskMembers live.1
    have hBindReady : ∀ p ∈ members, Corrupt.mem p = false ∧ live.1.mem p = true ∧
        SlotReadyForFreshBind subtreeHeight (net.slots p cIdx) rec := by
      intro p hp
      have hpQ : live.1.mem p = true := (mem_maskMembers_iff live.1 p).mp hp
      exact ⟨(hHonMem p hpQ).2, hpQ, hSlotsReady p hpQ⟩
    let net₁ := runQuorumJortsTrace H MAC macKeys Corrupt t subtreeHeight echoQuorum net
      (members.map (fun p => QuorumJortsTurn.bindSlot p live.1 rec))
    obtain ⟨hAfterBind, _⟩ :=
      runBindTurns_slots H MAC macKeys Corrupt t subtreeHeight echoQuorum cIdx live.1 rec hIdx
        members net (maskMembers_nodup live.1) hBindReady
    have hEchoReady : ∀ s ∈ members, Corrupt.mem s = false ∧ live.1.mem s = true ∧
        (net₁.slots s cIdx).walPoisoned = false ∧ (net₁.slots s cIdx).inFlight = some rec := by
      intro s hs
      have hsQ : live.1.mem s = true := (mem_maskMembers_iff live.1 s).mp hs
      obtain ⟨hP, hI, _⟩ := hAfterBind s hs
      exact ⟨(hHonMem s hsQ).2, hsQ, hP, hI⟩
    let net₂ := runQuorumJortsTrace H MAC macKeys Corrupt t subtreeHeight echoQuorum net₁
      (members.map (fun s => QuorumJortsTurn.emitSlotEcho s verifier live.1))
    obtain ⟨hSlotsEq, _, _⟩ :=
      runEchoTurns_emits H MAC macKeys Corrupt t subtreeHeight echoQuorum cIdx live.1 verifier rec hIdx
        members net₁ hEchoReady
    let bnd := beltRecordBinding H rec
    let echoes : List (QuorumCommitteeEcho n) :=
      members.map (fun s =>
        { fromParty := s
          toParty := verifier
          committeeIdx := cIdx
          epoch := rec.epoch
          binding := bnd
          mac := computeQuorumEchoMac MAC (macKeys s verifier) s.val verifier.val cIdx rec.epoch bnd })
    have hvMemList : verifier ∈ members := (mem_maskMembers_iff live.1 verifier).mpr hvInLive
    have hvHon : Corrupt.mem verifier = false := (hHonMem verifier hvInLive).2
    have hvPois : (net₂.slots verifier cIdx).walPoisoned = false := by
      rw [hSlotsEq]; exact (hAfterBind verifier hvMemList).1
    have hvInf : (net₂.slots verifier cIdx).inFlight = some rec := by
      rw [hSlotsEq]; exact (hAfterBind verifier hvMemList).2.1
    have hEpLt : rec.epoch.toNat < 2 ^ subtreeHeight :=
      (hSlotsReady verifier hvInLive).2.2.2.2.2.2.1
    have hValidSendersEq :
        validCommitteeEchoSenders H MAC macKeys cIdx verifier live.1 rec echoes = live.1 := by
      unfold validCommitteeEchoSenders
      apply congrArg CustodiansMask.mk; funext s
      cases hsQ : live.1.mem s
      · exact Bool.false_and _
      · simp only [Bool.true_and]
        apply List.any_eq_true.mpr
        refine ⟨{ fromParty := s, toParty := verifier, committeeIdx := cIdx, epoch := rec.epoch,
                  binding := bnd,
                  mac := computeQuorumEchoMac MAC (macKeys s verifier) s.val verifier.val cIdx rec.epoch bnd },
                List.mem_map.mpr ⟨s, (mem_maskMembers_iff live.1 s).mpr hsQ, rfl⟩, ?_⟩
        unfold verifyQuorumCommitteeEcho
        simp [bnd]
    have hPermOk :
        verifyCommitteeEchoPermit H MAC macKeys t subtreeHeight echoQuorum cIdx verifier live.1 rec echoes = true := by
      unfold verifyCommitteeEchoPermit
      rw [hValidSendersEq, live.2.1, hIdx, hvInLive]
      simp [hEpLt, hEqLeT]
    have hStepFinal :
        stepQuorumJorts H MAC macKeys Corrupt t subtreeHeight echoQuorum net₂
          (.releasePartitionedLeaf verifier live.1 rec echoes) =
        { net₂ with
          releasedLeaves :=
            { committee := live.1
              committeeIdx := cIdx
              localEpoch := rec.epoch
              globalLeaf := committeeGlobalLeaf (2 ^ subtreeHeight) cIdx rec.epoch.toNat
              verifier := verifier
              record := rec } :: net₂.releasedLeaves } := by
      unfold stepQuorumJorts
      simp only [hvHon, Bool.false_eq_true, ↓reduceIte]
      rw [hIdx]
      dsimp only
      have hGuardOk :
          (!(net₂.slots verifier cIdx).walPoisoned &&
            decide ((net₂.slots verifier cIdx).inFlight = some rec) &&
            verifyCommitteeEchoPermit H MAC macKeys t subtreeHeight echoQuorum cIdx verifier live.1 rec echoes) = true := by
        rw [hvPois, hvInf, hPermOk]
        simp
      rw [hGuardOk]
      rfl
    change (∀ p : Fin n, live.1.mem p = true →
      ((stepQuorumJorts H MAC macKeys Corrupt t subtreeHeight echoQuorum net₂
          (.releasePartitionedLeaf verifier live.1 rec echoes)).slots p cIdx).nextEpoch = rec.epoch.toNat + 1) ∧
      _ ∈ (stepQuorumJorts H MAC macKeys Corrupt t subtreeHeight echoQuorum net₂
          (.releasePartitionedLeaf verifier live.1 rec echoes)).releasedLeaves
    rw [hStepFinal]
    refine ⟨?_, .head _⟩
    intro p hpQ
    dsimp only
    rw [hSlotsEq]
    exact (hAfterBind p ((mem_maskMembers_iff live.1 p).mpr hpQ)).2.2

/-- **`#tooth` Under-Threshold `2 * q ≤ n + f` Permits Multi-Turn Split-View Equivocation
    (`tooth_quorum_jorts_under_threshold_split_view_across_turns`)**:
    1. **General `2 * q ≤ n + f` Split-View Partition**: Whenever `f < q ≤ n` and `2 * q ≤ n + f`,
       `prefixQuorumMask n q` and `suffixQuorumMask n q` each have size `q`, intersect in at most `f`
       corrupt custodians (`maskCard C ≤ f`), and have **zero honest intersection**!
    2. **Multi-Turn `(n = 3, f = 1, echoQuorum = 2)` & `(n = 5, f = 2, echoQuorum = 3)` Equivocation
       Traces on `QuorumJortsTurn`**: Over a shared global tree (`t = n`, `fullCustodiansMask n`),
       explicit multi-turn `List (QuorumJortsTurn 3)` and `List (QuorumJortsTurn 5)` executions
       release **two conflicting messages** (`rel₁.record.msgDigest ≠ rel₂.record.msgDigest`) on the
       **exact same `globalLeaf = 0`** across turns, with every echo attributed to an honest party
       genuinely emitted in `net.emittedEchoes` (`0` MAC forgeries)! -/
theorem tooth_quorum_jorts_under_threshold_split_view_across_turns :
    -- (1) General combinatorial split-view decomposition whenever 2 * q ≤ n + f:
    (∀ (n f q : Nat), f < q → q ≤ n → 2 * q ≤ n + f →
      let Q₁ := prefixQuorumMask n q
      let Q₂ := suffixQuorumMask n q
      let C := maskInter Q₁ Q₂
      maskCard Q₁ = q ∧
      maskCard Q₂ = q ∧
      maskCard C ≤ f ∧
      maskCard (maskDiff (maskInter Q₁ Q₂) C) = 0) ∧
    -- (2) Concrete multi-turn split-view equivocation on QuorumJortsTurn 3 (n = 3, f = 1, q = 2):
    (let H : List UInt8 → Digest256 := fun _ => 0xAA#256
     let MAC : Digest256 → List UInt8 → Digest256 := fun k _ => k
     let macKeys3 : Fin 3 → Fin 3 → Digest256 := fun i j => BitVec.ofNat 256 (10 * i.val + j.val + 1)
     let C3 : CustodiansMask 3 := ⟨fun i => decide (i.val = 1)⟩
     let Q3 : CustodiansMask 3 := fullCustodiansMask 3
     let p0 : Fin 3 := ⟨0, by decide⟩
     let p1 : Fin 3 := ⟨1, by decide⟩
     let p2 : Fin 3 := ⟨2, by decide⟩
     let rec₁ : BeltLatchRecord :=
       { epoch := 0, msgDigest := 0x1111#256, retrySalt := 0xAA#256, targetSumDigits := [1] }
     let rec₂ : BeltLatchRecord :=
       { epoch := 0, msgDigest := 0x2222#256, retrySalt := 0xBB#256, targetSumDigits := [2, 3] }
     let bnd₁ := beltRecordBinding H rec₁
     let bnd₂ := beltRecordBinding H rec₂
     let echoes₁ : List (QuorumCommitteeEcho 3) :=
       [ { fromParty := p0, toParty := p0, committeeIdx := 0, epoch := 0, binding := bnd₁,
           mac := computeQuorumEchoMac MAC (macKeys3 p0 p0) 0 0 0 0 bnd₁ },
         { fromParty := p1, toParty := p0, committeeIdx := 0, epoch := 0, binding := bnd₁,
           mac := computeQuorumEchoMac MAC (macKeys3 p1 p0) 1 0 0 0 bnd₁ } ]
     let echoes₂ : List (QuorumCommitteeEcho 3) :=
       [ { fromParty := p1, toParty := p2, committeeIdx := 0, epoch := 0, binding := bnd₂,
           mac := computeQuorumEchoMac MAC (macKeys3 p1 p2) 1 2 0 0 bnd₂ },
         { fromParty := p2, toParty := p2, committeeIdx := 0, epoch := 0, binding := bnd₂,
           mac := computeQuorumEchoMac MAC (macKeys3 p2 p2) 2 2 0 0 bnd₂ } ]
     let trace3 : List (QuorumJortsTurn 3) :=
       [ .bindSlot p0 Q3 rec₁,
         .emitSlotEcho p0 p0 Q3,
         .releasePartitionedLeaf p0 Q3 rec₁ echoes₁,
         .bindSlot p2 Q3 rec₂,
         .emitSlotEcho p2 p2 Q3,
         .releasePartitionedLeaf p2 Q3 rec₂ echoes₂ ]
     let net3 := runQuorumJortsTrace H MAC macKeys3 C3 3 4 2 (QuorumJortsNetworkState.init 3 4 2) trace3
     2 * 2 ≤ 3 + 1 ∧
     maskCard C3 = 1 ∧
     (∀ e ∈ echoes₁ ++ echoes₂, C3.mem e.fromParty = false → e ∈ net3.emittedEchoes) ∧
     ∃ rel₁ ∈ net3.releasedLeaves, ∃ rel₂ ∈ net3.releasedLeaves,
       rel₁.globalLeaf = 0 ∧
       rel₂.globalLeaf = 0 ∧
       rel₁.record.msgDigest ≠ rel₂.record.msgDigest) ∧
    -- (3) Concrete multi-turn split-view equivocation on QuorumJortsTurn 5 (n = 5, f = 2, q = 3):
    (let H : List UInt8 → Digest256 := fun _ => 0xAA#256
     let MAC : Digest256 → List UInt8 → Digest256 := fun k _ => k
     let macKeys5 : Fin 5 → Fin 5 → Digest256 := fun i j => BitVec.ofNat 256 (10 * i.val + j.val + 1)
     let C5 : CustodiansMask 5 := ⟨fun i => decide (i.val = 1 ∨ i.val = 2)⟩
     let Q5 : CustodiansMask 5 := fullCustodiansMask 5
     let q0 : Fin 5 := ⟨0, by decide⟩
     let q1 : Fin 5 := ⟨1, by decide⟩
     let q2 : Fin 5 := ⟨2, by decide⟩
     let q3 : Fin 5 := ⟨3, by decide⟩
     let rec₁ : BeltLatchRecord :=
       { epoch := 0, msgDigest := 0xAAAA#256, retrySalt := 0xCC#256, targetSumDigits := [1] }
     let rec₂ : BeltLatchRecord :=
       { epoch := 0, msgDigest := 0xBBBB#256, retrySalt := 0xDD#256, targetSumDigits := [2, 3] }
     let bnd₁ := beltRecordBinding H rec₁
     let bnd₂ := beltRecordBinding H rec₂
     let echoes₁ : List (QuorumCommitteeEcho 5) :=
       [ { fromParty := q0, toParty := q0, committeeIdx := 0, epoch := 0, binding := bnd₁,
           mac := computeQuorumEchoMac MAC (macKeys5 q0 q0) 0 0 0 0 bnd₁ },
         { fromParty := q1, toParty := q0, committeeIdx := 0, epoch := 0, binding := bnd₁,
           mac := computeQuorumEchoMac MAC (macKeys5 q1 q0) 1 0 0 0 bnd₁ },
         { fromParty := q2, toParty := q0, committeeIdx := 0, epoch := 0, binding := bnd₁,
           mac := computeQuorumEchoMac MAC (macKeys5 q2 q0) 2 0 0 0 bnd₁ } ]
     let echoes₂ : List (QuorumCommitteeEcho 5) :=
       [ { fromParty := q1, toParty := q3, committeeIdx := 0, epoch := 0, binding := bnd₂,
           mac := computeQuorumEchoMac MAC (macKeys5 q1 q3) 1 3 0 0 bnd₂ },
         { fromParty := q2, toParty := q3, committeeIdx := 0, epoch := 0, binding := bnd₂,
           mac := computeQuorumEchoMac MAC (macKeys5 q2 q3) 2 3 0 0 bnd₂ },
         { fromParty := q3, toParty := q3, committeeIdx := 0, epoch := 0, binding := bnd₂,
           mac := computeQuorumEchoMac MAC (macKeys5 q3 q3) 3 3 0 0 bnd₂ } ]
     let trace5 : List (QuorumJortsTurn 5) :=
       [ .bindSlot q0 Q5 rec₁,
         .emitSlotEcho q0 q0 Q5,
         .releasePartitionedLeaf q0 Q5 rec₁ echoes₁,
         .bindSlot q3 Q5 rec₂,
         .emitSlotEcho q3 q3 Q5,
         .releasePartitionedLeaf q3 Q5 rec₂ echoes₂ ]
     let net5 := runQuorumJortsTrace H MAC macKeys5 C5 5 4 3 (QuorumJortsNetworkState.init 5 4 2) trace5
     2 * 3 ≤ 5 + 2 ∧
     maskCard C5 = 2 ∧
     (∀ e ∈ echoes₁ ++ echoes₂, C5.mem e.fromParty = false → e ∈ net5.emittedEchoes) ∧
     ∃ rel₁ ∈ net5.releasedLeaves, ∃ rel₂ ∈ net5.releasedLeaves,
       rel₁.globalLeaf = 0 ∧
       rel₂.globalLeaf = 0 ∧
       rel₁.record.msgDigest ≠ rel₂.record.msgDigest) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n f q _hFq hQn hUnder Q₁ Q₂ C
    have hCard1 : maskCard Q₁ = q := maskCard_prefix n q hQn
    have hCard2 : maskCard Q₂ = q := by
      have hSuf := maskCard_ge_threshold n (n - q) (Nat.sub_le n q)
      change maskCard ⟨fun i : Fin n => decide (n - q ≤ i.val)⟩ = q
      rw [hSuf]
      omega
    have hCardC : maskCard C ≤ f := by
      change maskCard (maskInter Q₁ Q₂) ≤ f
      by_cases hDisj : q ≤ n - q
      · have hEmp : maskInter Q₁ Q₂ = emptyMask n := by
          apply congrArg CustodiansMask.mk; funext i
          change (decide (i.val < q) && decide (n - q ≤ i.val)) = false
          simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
          by_cases hi : i.val < q
          · right; omega
          · left; exact hi
        rw [hEmp, maskCard_empty]
        exact Nat.zero_le f
      · have hCover : (⟨fun i : Fin n => Q₁.mem i || Q₂.mem i⟩ : CustodiansMask n) =
            ⟨fun i : Fin n => decide (0 ≤ i.val)⟩ := by
          apply congrArg CustodiansMask.mk; funext i
          simp only [Q₁, Q₂, prefixQuorumMask, suffixQuorumMask, Nat.zero_le, decide_true,
            Bool.or_eq_true, decide_eq_true_eq]
          omega
        have hUI := maskCard_union_inter Q₁ Q₂
        rw [hCover, maskCard_ge_threshold n 0 (Nat.zero_le n), Nat.sub_zero, hCard1, hCard2] at hUI
        omega
    have hDiffZero : maskCard (maskDiff (maskInter Q₁ Q₂) C) = 0 := by
      have hEmp : maskDiff (maskInter Q₁ Q₂) C = emptyMask n := by
        apply congrArg CustodiansMask.mk; funext i
        change ((maskInter Q₁ Q₂).mem i && !(maskInter Q₁ Q₂).mem i) = false
        cases (maskInter Q₁ Q₂).mem i <;> rfl
      rw [hEmp, maskCard_empty]
    exact ⟨hCard1, hCard2, hCardC, hDiffZero⟩
  · decide
  · decide

/-! ### `G0-A`: `QS-A` (*Committee-Revealing Partitioned Custody*) vs `QS-B` (*Global-Tree Leaf Allocation*) -/

private theorem getElem?_of_maskPositionAux {n : Nat} (target : CustodiansMask n) :
    ∀ (xs : List (CustodiansMask n)) {idx : Nat},
      maskPositionAux target xs = some idx → xs[idx]? = some target
  | [], _, h => by cases h
  | x :: xs, idx, h => by
    simp only [maskPositionAux] at h
    if hx : x = target then
      simp only [hx, ↓reduceIte, Option.some.injEq] at h
      subst h
      simp [hx]
    else
      simp only [hx, ↓reduceIte, Option.map_eq_some_iff] at h
      obtain ⟨k, hk, rfl⟩ := h
      simpa using getElem?_of_maskPositionAux target xs hk

private theorem uint64_toNat_ofNat_of_lt {x : Nat} (h : x < 2 ^ 64) :
    (UInt64.ofNat x).toNat = x := by
  change (BitVec.ofNat 64 x).toNat = x
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- Lookup the `cIdx`-th `t`-committee in `chooseMasks n t`. -/
def committeeMaskAtIdx (n t cIdx : Nat) : Option (CustodiansMask n) :=
  (chooseMasks n t)[cIdx]?

theorem committeeMaskAtIdx_of_committeeIndexOf {n t cIdx : Nat} {Q : CustodiansMask n}
    (h : committeeIndexOf t Q = some cIdx) :
    committeeMaskAtIdx n t cIdx = some Q :=
  getElem?_of_maskPositionAux Q (chooseMasks n t) h

/-- Public committee extractor on `QuorumJortsSig`: recovers `selectedCommittee` directly from
    `sig.leaf` via `committeeOfLeaf` (`quorum_jorts.rs:190, 660-677`). -/
def committeeOfSignature (n t subtreeHeight : Nat) (sig : QuorumJortsSig) : Option (CustodiansMask n) :=
  match committeeOfLeaf (2 ^ subtreeHeight) (chooseMasks n t).length sig.leaf.toNat with
  | none => none
  | some cIdx => committeeMaskAtIdx n t cIdx

/-- Canonical single-signer `QuorumJorts` reference function parameterized by an explicit scheduled
    global leaf `gLeaf` (`quorumStagePkSeed`, `quorumStageChainSk`, `quorumChainStep`). -/
def quorumJortsReferenceSign
    (H : List UInt8 → Digest256)
    (masterSeed : Digest256)
    (gLeaf : UInt64)
    (counter : UInt32)
    (digits : List (Fin 4))
    (authPath : List Digest256) : QuorumJortsSig :=
  let pkSeed := quorumStagePkSeed H masterSeed
  let nodes := (List.finRange digits.length).map (fun idx =>
    let d := digits[idx.1]'(idx.2)
    let sk₀ := quorumStageChainSk H masterSeed gLeaf (UInt32.ofNat idx.1)
    wotsChainIter (quorumChainStep H pkSeed gLeaf) idx.1 0 d.val sk₀)
  { leaf := gLeaf
    counter := counter
    nodes := nodes
    authPath := authPath }

/-- Per-chain additive `t`-of-`t` XOR share randomness tape for `QS-A` partitioned custody. -/
abbrev QsAChainShareTape (t numChains : Nat) := Fin numChains → Fin (t - 1) → Digest256

/-- **Mode `QS-A` (*Committee-Revealing Partitioned Custody*) Signer**:
    Allocates `gLeaf = committeeGlobalLeaf (2 ^ subtreeHeight) cIdx localEpoch` inside
    `selectedCommittee`'s checked disjoint subtree. Independently shares the already stepped
    one-time chain nodes and reconstructs those nodes, never a reusable master-key share. -/
def qsAPartitionedSign {n : Nat}
    (H : List UInt8 → Digest256)
    (masterSeed : Digest256)
    (t subtreeHeight : Nat)
    (selectedCommittee : CustodiansMask n)
    (localEpoch : Nat)
    (counter : UInt32)
    (digits : List (Fin 4))
    (authPath : List Digest256)
    (shareTape : QsAChainShareTape t digits.length) : Option QuorumJortsSig :=
  match committeeIndexOf t selectedCommittee with
  | none => none
  | some cIdx =>
    if 0 < t ∧ localEpoch < 2 ^ subtreeHeight ∧
        committeeGlobalLeaf (2 ^ subtreeHeight) cIdx localEpoch < 2 ^ 64 then
      let gLeaf := UInt64.ofNat (committeeGlobalLeaf (2 ^ subtreeHeight) cIdx localEpoch)
      let pkSeed := quorumStagePkSeed H masterSeed
      let nodes := (List.finRange digits.length).map (fun idx =>
        let d := digits[idx.1]'(idx.2)
        let sk₀ := quorumStageChainSk H masterSeed gLeaf (UInt32.ofNat idx.1)
        let node := wotsChainIter (quorumChainStep H pkSeed gLeaf) idx.1 0 d.val sk₀
        xorFin256 t (dealAdditiveShares t node (shareTape idx)))
      some
        { leaf := gLeaf
          counter := counter
          nodes := nodes
          authPath := authPath }
    else none

/-- **Mode `QS-B` (*Global-Tree Quorum-Independent Leaf Allocation*) Signer**:
    Evaluates an explicitly scheduled `gLeaf` (allocation is external to this algebraic API), and
    reconstructs each 256-bit chain node `(lo, hi) ∈ GF(2^128)²` (`TowerElem 7 × TowerElem 7`) via
    Lagrange interpolation `ringDot lambdas` from the responding `t`-subset's points `pts`. -/
def qsBGlobalSign {d : Nat}
    (H : List UInt8 → Digest256)
    (masterSeed : Digest256)
    (gLeaf : UInt64)
    (counter : UInt32)
    (digits : List (Fin 4))
    (authPath : List Digest256)
    (polyTape : Fin digits.length → ShamirPadPoly (TowerElem 7) d × ShamirPadPoly (TowerElem 7) d)
    (pts lambdas : List (TowerElem 7)) : QuorumJortsSig :=
  let pkSeed := quorumStagePkSeed H masterSeed
  let nodes := (List.finRange digits.length).map (fun idx =>
    let dStep := digits[idx.1]'(idx.2)
    let sk₀ := quorumStageChainSk H masterSeed gLeaf (UInt32.ofNat idx.1)
    let trueNode := wotsChainIter (quorumChainStep H pkSeed gLeaf) idx.1 0 dStep.val sk₀
    if dStep.val < 3 then
      let (lo, hi) := unpackTower 8 trueNode
      let sharesLo := pts.map (fun x => RoundPoly.evalCoeffs (lo :: (polyTape idx).1.1) x)
      let sharesHi := pts.map (fun x => RoundPoly.evalCoeffs (hi :: (polyTape idx).2.1) x)
      packTower 8 (ringDot lambdas sharesLo, ringDot lambdas sharesHi)
    else
      trueNode)
  { leaf := gLeaf
    counter := counter
    nodes := nodes
    authPath := authPath }

/-- **`G0-A` Honesty / `#tooth` Theorem — `QS-A` Leaf Index Identifies `selectedCommittee` with
    Statistical Distance `1`, Contrasted Against `QS-B` Quorum-Independent Global Leaf Allocation
    (`qs_a_leaf_index_identifies_committee`)**:
    1. **Exact Committee Recovery (`committeeOfSignature = some selectedCommittee`)**: For every
       `selectedCommittee` (`committeeIndexOf t selectedCommittee = some cIdx`) and `localEpoch < 2 ^ subtreeHeight`
       (with `committeeGlobalLeaf < 2 ^ 64`), every signature `sig` emitted by `qsAPartitionedSign`
       satisfies `committeeOfLeaf ... sig.leaf.toNat = some cIdx` and
       `committeeOfSignature n t subtreeHeight sig = some selectedCommittee`!
    2. **Disjoint Support & Statistical Distance `1` (`Card > 0`)**: For any two distinct `t`-committees
       `Q₁ ≠ Q₂`, their `QS-A` output signatures have strictly disjoint `leaf` support (`sig₁.leaf ≠ sig₂.leaf`),
       and the public signature-only distinguisher `D(o) := (o.bind (committeeOfSignature n t subtreeHeight) == some Q₁)`
       achieves exact count `Card` on `Q₁` and `0` on `Q₂` (`(Card - 0) / Card = 1`, statistical distance `1`)!
    3. **Contrast with `QS-B` Global-Tree Quorum-Independent Leaf Allocation**: Under `qsBGlobalSign`
       on a quorum-independent global leaf `gLeaf`, any two `t`-quorums `(pts₁, lambdas₁)` and
       `(pts₂, lambdas₂)` with valid Vandermonde-at-zero Lagrange weights over `TowerElem 7` (`GF(2^128)`)
       emit the **bit-for-bit identical `QuorumJortsSig`** (`qsBGlobalSign ... pts₁ lambdas₁ = qsBGlobalSign ... pts₂ lambdas₂`)! -/
theorem qs_a_leaf_index_identifies_committee
    {n t subtreeHeight : Nat} (hTPos : 0 < t)
    (H : List UInt8 → Digest256) (masterSeed : Digest256) :
    -- (1) Exact committee recovery from sig.leaf in QS-A:
    (∀ (selectedCommittee : CustodiansMask n) (cIdx localEpoch : Nat)
       (counter : UInt32) (digits : List (Fin 4)) (authPath : List Digest256)
       (shareTape : QsAChainShareTape t digits.length),
      committeeIndexOf t selectedCommittee = some cIdx →
      localEpoch < 2 ^ subtreeHeight →
      committeeGlobalLeaf (2 ^ subtreeHeight) cIdx localEpoch < 2 ^ 64 →
      ∃ sig : QuorumJortsSig,
        qsAPartitionedSign H masterSeed t subtreeHeight selectedCommittee localEpoch
          counter digits authPath shareTape = some sig ∧
        committeeOfLeaf (2 ^ subtreeHeight) (chooseMasks n t).length sig.leaf.toNat = some cIdx ∧
        committeeOfSignature n t subtreeHeight sig = some selectedCommittee) ∧
    -- (2) Disjoint leaf support & statistical distance 1 between any two distinct committees Q₁ ≠ Q₂:
    (∀ (Q₁ Q₂ : CustodiansMask n) (cIdx₁ cIdx₂ ep₁ ep₂ : Nat)
       (cnt₁ cnt₂ : UInt32) (digits₁ digits₂ : List (Fin 4)) (ap₁ ap₂ : List Digest256),
      committeeIndexOf t Q₁ = some cIdx₁ →
      committeeIndexOf t Q₂ = some cIdx₂ →
      Q₁ ≠ Q₂ →
      ep₁ < 2 ^ subtreeHeight →
      ep₂ < 2 ^ subtreeHeight →
      committeeGlobalLeaf (2 ^ subtreeHeight) cIdx₁ ep₁ < 2 ^ 64 →
      committeeGlobalLeaf (2 ^ subtreeHeight) cIdx₂ ep₂ < 2 ^ 64 →
      (∀ (t₁ : QsAChainShareTape t digits₁.length) (t₂ : QsAChainShareTape t digits₂.length)
         (sig₁ sig₂ : QuorumJortsSig),
        qsAPartitionedSign H masterSeed t subtreeHeight Q₁ ep₁ cnt₁ digits₁ ap₁ t₁ = some sig₁ →
        qsAPartitionedSign H masterSeed t subtreeHeight Q₂ ep₂ cnt₂ digits₂ ap₂ t₂ = some sig₂ →
        sig₁.leaf ≠ sig₂.leaf) ∧
      (∀ (Card : Nat), 0 < Card →
        ∀ (enum₁ : SimpleEquiv (Fin Card) (QsAChainShareTape t digits₁.length))
          (enum₂ : SimpleEquiv (Fin Card) (QsAChainShareTape t digits₂.length)),
          let D : Option QuorumJortsSig → Bool := fun o =>
            match o with
            | none => false
            | some sig => decide (committeeOfSignature n t subtreeHeight sig = some Q₁)
          finSum Card (fun r =>
            if D (qsAPartitionedSign H masterSeed t subtreeHeight Q₁ ep₁ cnt₁ digits₁ ap₁ (enum₁.toFun r))
            then 1 else 0) = Card ∧
          finSum Card (fun r =>
            if D (qsAPartitionedSign H masterSeed t subtreeHeight Q₂ ep₂ cnt₂ digits₂ ap₂ (enum₂.toFun r))
            then 1 else 0) = 0)) ∧
    -- (3) Contrast with QS-B global-tree quorum-independent leaf allocation over GF(2^128):
    (∀ {d : Nat} (gLeaf : UInt64) (counter : UInt32) (digits : List (Fin 4)) (authPath : List Digest256)
       (polyTape : Fin digits.length → ShamirPadPoly (TowerElem 7) d × ShamirPadPoly (TowerElem 7) d)
       (pts₁ lambdas₁ pts₂ lambdas₂ : List (TowerElem 7)),
      ringDot lambdas₁ (pts₁.map (fun _ => CommRingOps.one)) = CommRingOps.one →
      (∀ deg, 1 ≤ deg → deg < d + 1 →
        ringDot lambdas₁ (pts₁.map (fun x => ringPow x deg)) = CommRingOps.zero) →
      ringDot lambdas₂ (pts₂.map (fun _ => CommRingOps.one)) = CommRingOps.one →
      (∀ deg, 1 ≤ deg → deg < d + 1 →
        ringDot lambdas₂ (pts₂.map (fun x => ringPow x deg)) = CommRingOps.zero) →
      qsBGlobalSign H masterSeed gLeaf counter digits authPath polyTape pts₁ lambdas₁ =
        quorumJortsReferenceSign H masterSeed gLeaf counter digits authPath ∧
      qsBGlobalSign H masterSeed gLeaf counter digits authPath polyTape pts₁ lambdas₁ =
        qsBGlobalSign H masterSeed gLeaf counter digits authPath polyTape pts₂ lambdas₂) := by
  have hPowPos : 0 < 2 ^ subtreeHeight := Nat.two_pow_pos subtreeHeight
  have hRecover : ∀ (Q : CustodiansMask n) (cIdx ep : Nat)
      (cnt : UInt32) (digits : List (Fin 4)) (ap : List Digest256)
      (tape : QsAChainShareTape t digits.length),
      committeeIndexOf t Q = some cIdx →
      ep < 2 ^ subtreeHeight →
      committeeGlobalLeaf (2 ^ subtreeHeight) cIdx ep < 2 ^ 64 →
      ∃ sig : QuorumJortsSig,
        qsAPartitionedSign H masterSeed t subtreeHeight Q ep cnt digits ap tape = some sig ∧
        sig.leaf.toNat = committeeGlobalLeaf (2 ^ subtreeHeight) cIdx ep ∧
        committeeOfLeaf (2 ^ subtreeHeight) (chooseMasks n t).length sig.leaf.toNat = some cIdx ∧
        committeeOfSignature n t subtreeHeight sig = some Q := by
    intro Q cIdx ep cnt digits ap tape hIdx hEpLt hFit
    have hcLt : cIdx < (chooseMasks n t).length := committeeIndexOf_lt hIdx
    have hMaskAt : committeeMaskAtIdx n t cIdx = some Q := committeeMaskAtIdx_of_committeeIndexOf hIdx
    unfold qsAPartitionedSign
    rw [hIdx]
    simp only [hTPos, hEpLt, hFit, and_self, ↓reduceIte]
    refine ⟨_, rfl, ?_, ?_, ?_⟩
    · exact uint64_toNat_ofNat_of_lt hFit
    · rw [uint64_toNat_ofNat_of_lt hFit]
      exact committeeOfLeaf_committeeGlobalLeaf hPowPos hcLt hEpLt
    · unfold committeeOfSignature
      rw [uint64_toNat_ofNat_of_lt hFit,
          committeeOfLeaf_committeeGlobalLeaf hPowPos hcLt hEpLt]
      exact hMaskAt
  refine ⟨?_, ?_, ?_⟩
  · intro selectedCommittee cIdx localEpoch counter digits authPath shareTape hIdx hEpLt hFit
    obtain ⟨sig, hSome, _, hOfLeaf, hOfSig⟩ :=
      hRecover selectedCommittee cIdx localEpoch counter digits authPath shareTape hIdx hEpLt hFit
    exact ⟨sig, hSome, hOfLeaf, hOfSig⟩
  · intro Q₁ Q₂ cIdx₁ cIdx₂ ep₁ ep₂ cnt₁ cnt₂ digits₁ digits₂ ap₁ ap₂
      hIdx₁ hIdx₂ hQNe hEp₁ hEp₂ hFit₁ hFit₂
    have hCIdxNe : cIdx₁ ≠ cIdx₂ := by
      intro hEq
      subst hEq
      exact hQNe (committeeIndexOf_inj hIdx₁ hIdx₂)
    refine ⟨?_, ?_⟩
    · intro t₁ t₂ sig₁ sig₂ hS₁ hS₂ hLeafEq
      obtain ⟨s₁, hSome₁, hNat₁, _, _⟩ := hRecover Q₁ cIdx₁ ep₁ cnt₁ digits₁ ap₁ t₁ hIdx₁ hEp₁ hFit₁
      obtain ⟨s₂, hSome₂, hNat₂, _, _⟩ := hRecover Q₂ cIdx₂ ep₂ cnt₂ digits₂ ap₂ t₂ hIdx₂ hEp₂ hFit₂
      rw [hSome₁] at hS₁; injection hS₁ with hEqS₁; subst hEqS₁
      rw [hSome₂] at hS₂; injection hS₂ with hEqS₂; subst hEqS₂
      have hGL : committeeGlobalLeaf (2 ^ subtreeHeight) cIdx₁ ep₁ =
                 committeeGlobalLeaf (2 ^ subtreeHeight) cIdx₂ ep₂ := by
        rw [← hNat₁, ← hNat₂, hLeafEq]
      exact hCIdxNe (committee_leaf_ranges_disjoint hEp₁ hEp₂ hGL).1
    · intro Card _hCardPos enum₁ enum₂ D
      refine ⟨?_, ?_⟩
      · have hEach₁ : ∀ r : Fin Card,
            (if D (qsAPartitionedSign H masterSeed t subtreeHeight Q₁ ep₁ cnt₁ digits₁ ap₁ (enum₁.toFun r))
             then 1 else 0) = 1 := by
          intro r
          obtain ⟨sig₁, hSome₁, _, _, hOfSig₁⟩ :=
            hRecover Q₁ cIdx₁ ep₁ cnt₁ digits₁ ap₁ (enum₁.toFun r) hIdx₁ hEp₁ hFit₁
          rw [hSome₁]
          have hD₁ : D (some sig₁) = true := by
            dsimp only [D]
            exact decide_eq_true hOfSig₁
          simp only [hD₁, ↓reduceIte]
        rw [finSum_congr hEach₁, finSum_const, Nat.mul_one]
      · have hEach₂ : ∀ r : Fin Card,
            (if D (qsAPartitionedSign H masterSeed t subtreeHeight Q₂ ep₂ cnt₂ digits₂ ap₂ (enum₂.toFun r))
             then 1 else 0) = 0 := by
          intro r
          obtain ⟨sig₂, hSome₂, _, _, hOfSig₂⟩ :=
            hRecover Q₂ cIdx₂ ep₂ cnt₂ digits₂ ap₂ (enum₂.toFun r) hIdx₂ hEp₂ hFit₂
          rw [hSome₂]
          have hSomeNe : (some Q₂ : Option (CustodiansMask n)) ≠ some Q₁ :=
            fun h => hQNe (Option.some.inj h).symm
          have hD₂ : D (some sig₂) = false := by
            dsimp only [D]
            rw [hOfSig₂]
            exact decide_eq_false hSomeNe
          simp only [hD₂, Bool.false_eq_true, ↓reduceIte]
        rw [finSum_congr hEach₂, finSum_const, Nat.mul_zero]
  · intro d gLeaf counter digits authPath polyTape pts₁ lambdas₁ pts₂ lambdas₂ hZ₁ hH₁ hZ₂ hH₂
    have hRefEq : ∀ (pts lambdas : List (TowerElem 7)),
        ringDot lambdas (pts.map (fun _ => CommRingOps.one)) = CommRingOps.one →
        (∀ deg, 1 ≤ deg → deg < d + 1 →
          ringDot lambdas (pts.map (fun x => ringPow x deg)) = CommRingOps.zero) →
        qsBGlobalSign H masterSeed gLeaf counter digits authPath polyTape pts lambdas =
          quorumJortsReferenceSign H masterSeed gLeaf counter digits authPath := by
      intro pts lambdas hZ hH
      dsimp only [qsBGlobalSign, quorumJortsReferenceSign]
      congr 1
      apply List.map_congr_left
      intro idx _
      if hd : (digits[idx.1]'(idx.2)).val < 3 then
        simp only [hd, ↓reduceIte]
        let sk₀ := quorumStageChainSk H masterSeed gLeaf (UInt32.ofNat idx.1)
        let pkSeed := quorumStagePkSeed H masterSeed
        let trueNode := wotsChainIter (quorumChainStep H pkSeed gLeaf) idx.1 0 (digits[idx.1]'(idx.2)).val sk₀
        change (match unpackTower 8 trueNode with
          | (lo, hi) =>
            packTower 8
              (ringDot lambdas (pts.map (fun x => RoundPoly.evalCoeffs (lo :: (polyTape idx).1.1) x)),
               ringDot lambdas (pts.map (fun x => RoundPoly.evalCoeffs (hi :: (polyTape idx).2.1) x)))) =
          trueNode
        rcases hUnp : unpackTower 8 trueNode with ⟨lo, hi⟩
        dsimp only
        have hLenLo : (lo :: (polyTape idx).1.1).length ≤ d + 1 := by
          simp [(polyTape idx).1.2]
        have hLenHi : (hi :: (polyTape idx).2.1).length ≤ d + 1 := by
          simp [(polyTape idx).2.2]
        have hLo : ringDot lambdas (pts.map (fun x =>
            RoundPoly.evalCoeffs (lo :: (polyTape idx).1.1) x)) = lo := by
          rw [lagrangeAtZero_evalCoeffs lambdas pts _ (d + 1) hLenLo hZ hH]
          simp [LawfulCommRing.zero_mul, LawfulCommRing.add_zero]
        have hHi : ringDot lambdas (pts.map (fun x =>
            RoundPoly.evalCoeffs (hi :: (polyTape idx).2.1) x)) = hi := by
          rw [lagrangeAtZero_evalCoeffs lambdas pts _ (d + 1) hLenHi hZ hH]
          simp [LawfulCommRing.zero_mul, LawfulCommRing.add_zero]
        rw [hLo, hHi, ← hUnp]
        exact packTower_unpackTower 8 trueNode
      else
        simp only [hd, ↓reduceIte]
    have h1 := hRefEq pts₁ lambdas₁ hZ₁ hH₁
    have h2 := hRefEq pts₂ lambdas₂ hZ₂ hH₂
    exact ⟨h1, h1.trans h2.symm⟩

/-- **`G0-A` Positive Reference Theorem — `QS-A` Single-Signer Equivalence Conditional on the Same
    Leaf Schedule (`qs_a_single_signer_equiv_given_same_leaf_schedule`)**:
    When `0 < t`, `committeeIndexOf t selectedCommittee = some cIdx`, and the standalone single-key
    reference signer `quorumJortsReferenceSign` is parameterized with the **exact same
    committee-assigned leaf schedule** `gLeaf = UInt64.ofNat (committeeGlobalLeaf (2 ^ subtreeHeight) cIdx localEpoch)`:
    1. **Pointwise Exact Signature Refinement**: For EVERY additive XOR share tape `shareTape`,
       `qsAPartitionedSign` outputs `some (quorumJortsReferenceSign H masterSeed gLeaf counter digits authPath)`!
    2. **Exact `0` Statistical Distance Conditional on Same Leaf Schedule**: Over any finite share
       randomness space `Card` (`enum : SimpleEquiv (Fin Card) (QsAChainShareTape t digits.length)`)
       and any distinguisher `D : Option QuorumJortsSig → Bool`, `finSum` counts are identically equal! -/
theorem qs_a_single_signer_equiv_given_same_leaf_schedule
    {n t subtreeHeight : Nat} (hTPos : 0 < t)
    (H : List UInt8 → Digest256) (masterSeed : Digest256)
    (selectedCommittee : CustodiansMask n) (cIdx localEpoch : Nat)
    (hIdx : committeeIndexOf t selectedCommittee = some cIdx)
    (hEpoch : localEpoch < 2 ^ subtreeHeight)
    (hFit : committeeGlobalLeaf (2 ^ subtreeHeight) cIdx localEpoch < 2 ^ 64)
    (counter : UInt32) (digits : List (Fin 4)) (authPath : List Digest256) :
    let gLeaf := UInt64.ofNat (committeeGlobalLeaf (2 ^ subtreeHeight) cIdx localEpoch)
    let refSig := quorumJortsReferenceSign H masterSeed gLeaf counter digits authPath
    (∀ shareTape : QsAChainShareTape t digits.length,
      qsAPartitionedSign H masterSeed t subtreeHeight selectedCommittee localEpoch
        counter digits authPath shareTape = some refSig) ∧
    (∀ (Card : Nat) (enum : SimpleEquiv (Fin Card) (QsAChainShareTape t digits.length))
       (D : Option QuorumJortsSig → Bool),
      finSum Card (fun r =>
        if D (qsAPartitionedSign H masterSeed t subtreeHeight selectedCommittee localEpoch
                counter digits authPath (enum.toFun r)) then 1 else 0) =
      finSum Card (fun _ => if D (some refSig) then 1 else 0)) := by
  intro gLeaf refSig
  have hPointwise : ∀ shareTape : QsAChainShareTape t digits.length,
      qsAPartitionedSign H masterSeed t subtreeHeight selectedCommittee localEpoch
        counter digits authPath shareTape = some refSig := by
    intro shareTape
    unfold qsAPartitionedSign
    rw [hIdx]
    simp only [hTPos, hEpoch, hFit, and_self, ↓reduceIte]
    congr 1
    unfold refSig quorumJortsReferenceSign
    congr 1
    apply List.map_congr_left
    intro idx _
    dsimp only
    rw [reconstruct_dealAdditiveShares t hTPos]
  refine ⟨hPointwise, ?_⟩
  intro Card enum D
  apply finSum_congr
  intro r
  rw [hPointwise (enum.toFun r)]

/-! ## §3. Self-Verifying Pre-Stepped `(t, n)` Shamir `WOTS+C` Table over `GF(2^128)` (`TowerElem 7`) & 256-Bit `Digest256` (`v = 128`, `S = 192`) -/

/-- Base `w = 4` (`2` bits per chain digit) of `quorum_jorts.rs:68`. -/
def quorumWotsBase : Nat := 4

/-- Chain step bound `w - 1 = 3` of `quorum_jorts.rs:69`. -/
def quorumWotsSteps : Nat := 3

/-- Full 256-bit chain count `v = 128` (`128 * 2 = 256` bits) of `quorum_jorts.rs:70`. -/
def quorumWotsChains : Nat := 128

/-- Balanced 256-bit `WOTS+C` target digit sum `S = 128 * 3 / 2 = 192` of `quorum_jorts.rs:71`. -/
def quorumWotsTargetSum : Nat := 192

/-- Bit offset of chain digit `i` inside the digest: byte `i / 4` (byte zero occupies the high
    eight bits), and within that byte the shifts `6, 4, 2, 0` in that order. -/
def quorumDibitShift (i : Nat) : Nat := 8 * (31 - i / 4) + (6 - 2 * (i % 4))

/-- Chain digit `i` of a 256-bit grinding digest, most-significant dibit first within each byte:
    `(digest[i / 4] >> (6 - 2 * (i % 4))) & 3`, as in `digits_at` of `quorum_jorts.rs`. -/
def quorumDigitAt (dig : Digest256) (i : Nat) : Fin 4 :=
  ⟨((dig >>> quorumDibitShift i).toNat) % 4, Nat.mod_lt _ (by decide)⟩

/-- Extract `v = 128` base-4 digits from a 256-bit grinding digest in the order of `digits_at`
    (`quorum_jorts.rs`): bytes in order, and the four dibits of each byte from the top down. -/
def quorumDigitsFromDigest (dig : Digest256) : List (Fin 4) :=
  (List.range quorumWotsChains).map (quorumDigitAt dig)

private theorem be_getElem_toNat (w n i : Nat) (hi : i < w) :
    ((be w n)[i]'(by simpa using hi)).toNat = n / 256 ^ (w - 1 - i) % 256 := by
  induction w generalizing n i with
  | zero => omega
  | succ w ih =>
    by_cases h : i < w
    · have hl : i < (be w (n / 256)).length := by rw [length_be]; exact h
      simp only [be, List.getElem_append_left hl]
      rw [ih (n / 256) i h, Nat.div_div_eq_div_mul]
      have he : w + 1 - 1 - i = (w - 1 - i) + 1 := by omega
      rw [he, Nat.pow_succ, Nat.mul_comm 256]
    · have he : i = w := by omega
      subst i
      simp [be, List.getElem_append_right, length_be, UInt8.toNat_ofNat']

/-- Correspondence to the actual encoded digest bytes, not merely another Lean extractor. -/
theorem quorumDigitAt_eq_encoded_byte (dig : Digest256) (i : Fin 128) :
    (quorumDigitAt dig i.val).val =
      (((encodeDigest256 dig)[i.val / 4]'(by
        rw [encodeDigest256_length]; have := i.isLt; omega)).toNat >>>
        (6 - 2 * (i.val % 4))) % 4 := by
  have hb : i.val / 4 < 32 := by have := i.isLt; omega
  have hbyte := be_getElem_toNat 32 dig.toNat (i.val / 4) hb
  change (quorumDigitAt dig i.val).val =
    (((be 32 dig.toNat)[i.val / 4]'(by simpa using hb)).toNat >>>
      (6 - 2 * (i.val % 4))) % 4
  rw [hbyte]
  -- The two-bit shift splits into a byte shift and a shift within that byte.
  have hr : i.val % 4 < 4 := Nat.mod_lt _ (by decide)
  change (dig >>> (8 * (31 - i.val / 4) + (6 - 2 * (i.val % 4)))).toNat % 4 = _
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_add]
  simp only [Nat.shiftRight_eq_div_pow]
  have hp : (256 : Nat) ^ (31 - i.val / 4) = 2 ^ (8 * (31 - i.val / 4)) := by
    rw [Nat.pow_mul]
  rw [hp]
  generalize dig.toNat / 2 ^ (8 * (31 - i.val / 4)) = m
  generalize i.val % 4 = r at hr
  have casesR : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
  rcases casesR with rfl | rfl | rfl | rfl <;>
    simp only [Nat.reduceMul, Nat.reduceSub, Nat.reducePow] <;> omega

/-- `quorumDigitAt` is the byte-level expression `(byte >> shift) & 3`, where the byte is
    `digest[i / 4]` and the shift is `6 - 2 * (i % 4)`. -/
theorem quorumDigitAt_eq_byte_shift (dig : Digest256) (i : Nat) :
    (quorumDigitAt dig i).val =
      (((dig >>> (8 * (31 - i / 4))).toNat % 256) >>> (6 - 2 * (i % 4))) % 4 := by
  have h : i % 4 < 4 := Nat.mod_lt _ (by decide)
  show (dig >>> (8 * (31 - i / 4) + (6 - 2 * (i % 4)))).toNat % 4 = _
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ushiftRight, Nat.shiftRight_add]
  simp only [Nat.shiftRight_eq_div_pow]
  generalize dig.toNat / 2 ^ (8 * (31 - i / 4)) = m
  generalize i % 4 = r at h
  have hr : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
  rcases hr with rfl | rfl | rfl | rfl <;>
    simp only [Nat.reduceMul, Nat.reduceSub, Nat.reducePow] <;> omega

/-- `quorumDigitAt` as a two-bit field of the digest at `quorumDibitShift i`. The right-hand side
    is the expression `wotsCDibits128_byte_shift` proves for the `WOTS+C` extractor
    `wotsCDibits128`, so the two extractors read the same dibit for every chain index. -/
theorem quorumDigitAt_eq_extractLsb' (dig : Digest256) (i : Nat) :
    (quorumDigitAt dig i).val =
      (dig.extractLsb' (8 * (31 - i / 4) + (6 - 2 * (i % 4))) 2).toNat := by
  show (dig >>> quorumDibitShift i).toNat % 4 = (dig.toNat >>> quorumDibitShift i) % 2 ^ 2
  rfl

/-- Sanity vector: the first byte `0xE4 = 0b11_10_01_00` decodes as `[3, 2, 1, 0]`, as in the
    signer. -/
theorem quorumDigitsFromDigest_msb_sanity :
    ((quorumDigitsFromDigest (0xE4#256 <<< 248)).take 4).map Fin.val = [3, 2, 1, 0] := by
  decide +kernel

/-- `#tooth` Dibit Order (`tooth_quorumDigits_not_lsb_first`): reading the dibits of `0xE4` from
    the low end of the digest gives `[0, 1, 2, 3]`, which is not what `quorumDigitsFromDigest`
    returns. -/
theorem tooth_quorumDigits_not_lsb_first :
    (List.range 4).map (fun i => ((0xE4#256 : Digest256) >>> (2 * i)).toNat % 4) = [0, 1, 2, 3] ∧
    ((quorumDigitsFromDigest (0xE4#256 <<< 248)).take 4).map Fin.val ≠ [0, 1, 2, 3] := by
  decide +kernel

theorem quorumDigitsFromDigest_length (dig : Digest256) :
    (quorumDigitsFromDigest dig).length = 128 := by
  simp [quorumDigitsFromDigest, quorumWotsChains]


/-- Adapt big-endian byte positions to Baggy's low-byte-first digest representation. -/
def quorumWotsIndex (i : Fin 128) : Fin 128 :=
  ⟨4 * (31 - i.val / 4) + i.val % 4, by have := i.isLt; omega⟩

/-- The quorum schedule is exactly the WOTS+C production schedule, at every chain. -/
theorem quorumDigitAt_eq_wotsCDibits128 (dig : Digest256) (i : Fin 128) :
    quorumDigitAt dig i.val = wotsCDibits128 dig (quorumWotsIndex i) := by
  apply Fin.ext
  rw [quorumDigitAt_eq_extractLsb', wotsCDibits128_byte_shift]
  have hi := i.isLt
  have hdiv : (quorumWotsIndex i).val / 4 = 31 - i.val / 4 := by
    dsimp [quorumWotsIndex]; omega
  have hmod : (quorumWotsIndex i).val % 4 = i.val % 4 := by
    dsimp [quorumWotsIndex]; omega
  rw [hdiv, hmod]
  rfl

/-- The list passed to the quorum signer uses the WOTS+C chain order. -/
theorem quorumDigitsFromDigest_get (dig : Digest256) (i : Fin 128) :
    (quorumDigitsFromDigest dig)[i.val]'(by rw [quorumDigitsFromDigest_length]; exact i.isLt) =
      wotsCDibits128 dig (quorumWotsIndex i) := by
  simp only [quorumDigitsFromDigest, List.getElem_map, List.getElem_range]
  exact quorumDigitAt_eq_wotsCDibits128 dig i

/-- Message-bound quorum signing entry: the counter digest must pass the WOTS+C target sum
    check before the existing reference signer receives its extracted chain schedule. -/
def quorumJortsSignMessage (H : List UInt8 → Digest256) (masterSeed : Digest256)
    (pk : QuorumPublicKey) (leaf : UInt64) (counter : UInt32)
    (msg : List UInt8) (authPath : List Digest256) : Option QuorumJortsSig :=
  let dig := quorumCounterDigest H (quorumMessageHash H pk leaf msg) counter
  match wotsC256DecodeValidDigest dig with
  | none => none
  | some _ => some (quorumJortsReferenceSign H masterSeed leaf counter
      (quorumDigitsFromDigest dig) authPath)

/-- Accepted digest decoding connects the actual signer list to the validated WOTS+C digits. -/
theorem quorumJortsSignMessage_schedule (H : List UInt8 → Digest256) (masterSeed : Digest256)
    (pk : QuorumPublicKey) (leaf : UInt64) (counter : UInt32)
    (msg : List UInt8) (authPath : List Digest256) (d : WotsC256Digits)
    (h : wotsC256DecodeValidDigest
      (quorumCounterDigest H (quorumMessageHash H pk leaf msg) counter) = some d) :
    quorumJortsSignMessage H masterSeed pk leaf counter msg authPath =
      some (quorumJortsReferenceSign H masterSeed leaf counter
        (quorumDigitsFromDigest (quorumCounterDigest H (quorumMessageHash H pk leaf msg) counter))
        authPath) ∧
    ∀ i : Fin 128, quorumDigitAt
      (quorumCounterDigest H (quorumMessageHash H pk leaf msg) counter) i.val = d.digits (quorumWotsIndex i) := by
  refine ⟨by simp only [quorumJortsSignMessage, h], ?_⟩
  intro i
  rw [wotsC256DecodeValidDigest_some_digits h]
  exact quorumDigitAt_eq_wotsCDibits128 _ i

/-- Rejected target sums never reach chain signing. -/
theorem quorumJortsSignMessage_rejects (H : List UInt8 → Digest256) (masterSeed : Digest256)
    (pk : QuorumPublicKey) (leaf : UInt64) (counter : UInt32)
    (msg : List UInt8) (authPath : List Digest256)
    (h : wotsC256DecodeValidDigest
      (quorumCounterDigest H (quorumMessageHash H pk leaf msg) counter) = none) :
    quorumJortsSignMessage H masterSeed pk leaf counter msg authPath = none := by
  simp only [quorumJortsSignMessage, h]

private theorem foldr_add_replicate_acc : ∀ (n val acc : Nat),
    (List.replicate n val).foldr (· + ·) acc = n * val + acc
  | 0, _, acc => by simp
  | n + 1, val, acc => by
    simp only [List.replicate_succ, List.foldr_cons, foldr_add_replicate_acc n val acc, Nat.add_one_mul]
    omega

private theorem map_finRange_threshold :
    ∀ (n m u v : Nat), m ≤ n →
      (List.finRange n).map (fun i : Fin n => if i.val < m then u else v) =
        List.replicate m u ++ List.replicate (n - m) v
  | 0, m, _, _, hm => by
    have hm0 : m = 0 := Nat.eq_zero_of_le_zero hm
    subst hm0
    simp
  | n + 1, 0, u, v, _ => by
    rw [List.finRange_succ, List.map_cons, List.map_map]
    have hHead : (if (0 : Fin (n + 1)).val < 0 then u else v) = v := by simp
    have hTail : ((fun i : Fin (n + 1) => if i.val < 0 then u else v) ∘ Fin.succ) =
        (fun i : Fin n => if i.val < 0 then u else v) := by
      funext i; simp
    rw [hHead, hTail, map_finRange_threshold n 0 u v (Nat.zero_le n)]
    simp [List.replicate_succ]
  | n + 1, m + 1, u, v, hm => by
    rw [List.finRange_succ, List.map_cons, List.map_map]
    have hHead : (if (0 : Fin (n + 1)).val < m + 1 then u else v) = u := by simp
    have hTail : ((fun i : Fin (n + 1) => if i.val < m + 1 then u else v) ∘ Fin.succ) =
        (fun i : Fin n => if i.val < m then u else v) := by
      funext i
      simp only [Function.comp_apply, Fin.val_succ, Nat.add_lt_add_iff_right]
    rw [hHead, hTail, map_finRange_threshold n m u v (Nat.le_of_succ_le_succ hm),
        Nat.succ_sub_succ_eq_sub, List.replicate_succ, List.cons_append]

/-- **`#tooth` 256-Bit `QuorumJorts` `WOTS+C` Parameter Sanity (`tooth_impossible_wots128_target_sum_385_vs_valid_192`)**:
    For `v = 128` chains in base `w = 4` (`d_i ∈ {0, 1, 2, 3}`), the maximum possible digit sum is
    `128 * 3 = 384`, so target sum `385` is **strictly uninhabited**, whereas `WOTS_TARGET_SUM = 192`
    (`quorum_jorts.rs:71`) is inhabited (both by `64 × 3 + 64 × 0` and by `64 × 2 + 64 × 1` where
    every chain opens an online `GF(2^128)` Shamir polynomial)! -/
theorem tooth_impossible_wots128_target_sum_385_vs_valid_192 :
    (∀ d : List Nat, validWotsCsCodeword 128 4 385 d → False) ∧
    validWotsCsCodeword 128 4 192 (List.replicate 64 3 ++ List.replicate 64 0) ∧
    validWotsCsCodeword 128 4 192 (List.replicate 64 2 ++ List.replicate 64 1) := by
  have hBound : ∀ (xs : List Nat), (∀ x ∈ xs, x < 4) → xs.foldr (· + ·) 0 ≤ xs.length * 3 := by
    intro xs hLt
    induction xs with
    | nil => simp
    | cons x rest ih =>
      have hx := hLt x (.head rest)
      have hRest := ih (fun y hy => hLt y (.tail x hy))
      simp only [List.foldr_cons, List.length_cons]
      have hMul : (rest.length + 1) * 3 = rest.length * 3 + 3 := by omega
      omega
  refine ⟨?_, ?_, ?_⟩
  · intro d ⟨hLen, hDigits, hSum⟩
    have hMax := hBound d hDigits
    rw [hLen, hSum] at hMax
    omega
  · unfold validWotsCsCodeword
    refine ⟨by simp, ?_, by rw [List.foldr_append, foldr_add_replicate_acc, foldr_add_replicate_acc]⟩
    intro x hx
    rcases List.mem_append.mp hx with h3 | h0
    · rw [List.eq_of_mem_replicate h3]; decide
    · rw [List.eq_of_mem_replicate h0]; decide
  · unfold validWotsCsCodeword
    refine ⟨by simp, ?_, by rw [List.foldr_append, foldr_add_replicate_acc, foldr_add_replicate_acc]⟩
    intro x hx
    rcases List.mem_append.mp hx with h2 | h1
    · rw [List.eq_of_mem_replicate h2]; decide
    · rw [List.eq_of_mem_replicate h1]; decide

/-- **`#tooth` `WOTS+C` Parameter Sanity (`tooth_impossible_wots4_target_sum_215_vs_valid_87`)**:
    For `L = 58` chains in base `w = 4` (`d_i ∈ {0, 1, 2, 3}`), the maximum possible digit sum is
    `58 * 3 = 174`, so target sum `215` is **strictly uninhabited**, whereas the balanced
    target `S = 58 * 3 / 2 = 87` is inhabited. -/
theorem tooth_impossible_wots4_target_sum_215_vs_valid_87 :
    (∀ d : List Nat, validWotsCsCodeword 58 4 215 d → False) ∧
    validWotsCsCodeword 58 4 87 (List.replicate 29 3 ++ List.replicate 29 0) := by
  have hBound : ∀ (xs : List Nat), (∀ x ∈ xs, x < 4) → xs.foldr (· + ·) 0 ≤ xs.length * 3 := by
    intro xs hLt
    induction xs with
    | nil => simp
    | cons x rest ih =>
      have hx := hLt x (.head rest)
      have hRest := ih (fun y hy => hLt y (.tail x hy))
      simp only [List.foldr_cons, List.length_cons]
      have hMul : (rest.length + 1) * 3 = rest.length * 3 + 3 := by omega
      omega
  refine ⟨?_, ?_⟩
  · intro d ⟨hLen, hDigits, hSum⟩
    have hMax := hBound d hDigits
    rw [hLen, hSum] at hMax
    omega
  · unfold validWotsCsCodeword
    refine ⟨by decide, ?_, by decide⟩
    intro x hx
    rcases List.mem_append.mp hx with h3 | h0
    · rw [List.eq_of_mem_replicate h3]; decide
    · rw [List.eq_of_mem_replicate h0]; decide

/-- Secret intermediate chain positions `(y_i^(0), y_i^(1), y_i^(2))` for `w = 4` across `L` chains
    (step `3` is the public chain endpoint `pk_i` committed in the `Jorts` Merkle leaf). -/
abbrev PreSteppedChainSecrets (R : Type) (L : Nat) := Fin L → Fin 3 → R

/-- Independent degree-`≤ d` (`d = t - 1`) Shamir sharing randomness per `(chain i, step k)`. -/
abbrev PreSteppedShamirTape (R : Type) (d L : Nat) := Fin L → Fin 3 → ShamirPadPoly R d

/-- Complete `(t - 1)`-collusion adversary view during online `Jorts` Mode 3B signing:
    1. `corruptTableShares`: background Shamir shares at `corruptPts` for ALL `3` secret steps
       `(y_i^(0), y_i^(1), y_i^(2))` across all `L` chains;
    2. `onlineOpenedPolys`: full degree-`≤ d` polynomial `y_i^(d_i) :: (tape i d_i).1` opened
       online ONLY at the single selected step `d_i` (when `d_i < 3`; `none` when `d_i = 3`). -/
structure PreSteppedAdvView (R : Type) (L : Nat) where
  corruptTableShares : Fin L → Fin 3 → List R
  onlineOpenedPolys : Fin L → Option (List R)

/-- Compute the adversary's view from `(corruptPts, digits, y, tape)`. -/
def computePreSteppedAdvView {R : Type} [CommRingOps R] {d L : Nat}
    (corruptPts : List R) (digits : Fin L → Fin 4)
    (y : PreSteppedChainSecrets R L) (tape : PreSteppedShamirTape R d L) :
    PreSteppedAdvView R L where
  corruptTableShares i k :=
    corruptPts.map (fun xc => RoundPoly.evalCoeffs (y i k :: (tape i k).1) xc)
  onlineOpenedPolys i :=
    if h : (digits i).val < 3 then
      some (y i ⟨(digits i).val, h⟩ :: (tape i ⟨(digits i).val, h⟩).1)
    else
      none

/-- Single-entry Shamir secret-shift bijection: shifts constant term `s₁ ↦ s₂` while keeping all
    evaluations at `corruptPts` (`|corruptPts| ≤ d`) invariant (`0 Classical.choice`). -/
def shamirSecretShiftEquiv {R : Type} [LawfulCommRing R]
    (inv : R → R) (d : Nat) (corruptPts : List R)
    (s₁ s₂ : R) (hCard : corruptPts.length + 1 ≤ d + 1) :
    SimpleEquiv (ShamirPadPoly R d) (ShamirPadPoly R d) :=
  let eqv₁ := shamirShare_rebalanceEquiv inv d corruptPts s₁ hCard
  let eqv₂ := shamirShare_rebalanceEquiv inv d corruptPts s₂ hCard
  { toFun := fun A => eqv₂.invFun (eqv₁.toFun A)
    invFun := fun B => eqv₁.invFun (eqv₂.toFun B)
    left_inv := fun A => by rw [eqv₂.right_inv, eqv₁.left_inv]
    right_inv := fun B => by rw [eqv₁.right_inv, eqv₂.left_inv] }

theorem shamirSecretShiftEquiv_preserves_corruptShares {R : Type} [LawfulCommRing R]
    (inv : R → R) (hInv : ∀ x : R, x ≠ CommRingOps.zero → CommRingOps.mul x (inv x) = CommRingOps.one)
    (d : Nat) (corruptPts : List R)
    (s₁ s₂ : R) (hCard : corruptPts.length + 1 ≤ d + 1)
    (hNonZero : ∀ c ∈ corruptPts, c ≠ CommRingOps.zero)
    (A : ShamirPadPoly R d) :
    let A' := (shamirSecretShiftEquiv inv d corruptPts s₁ s₂ hCard).toFun A
    ∀ xc ∈ corruptPts,
      RoundPoly.evalCoeffs (s₂ :: A'.1) xc = RoundPoly.evalCoeffs (s₁ :: A.1) xc := by
  intro A' xc hxc
  let zeroPad : ShamirPadPoly R (d + 1) :=
    ⟨List.replicate (d + 1) CommRingOps.zero, List.length_replicate⟩
  let eqv₁ := shamirShare_rebalanceEquiv inv d corruptPts s₁ hCard
  let eqv₂ := shamirShare_rebalanceEquiv inv d corruptPts s₂ hCard
  have h1 := (shamir_share_pad_rebalance inv hInv d corruptPts s₁ hCard hNonZero A zeroPad).1 xc hxc
  have h2 := (shamir_share_pad_rebalance inv hInv d corruptPts s₂ hCard hNonZero A' zeroPad).1 xc hxc
  have hMid : eqv₂.toFun A' = eqv₁.toFun A := eqv₂.right_inv (eqv₁.toFun A)
  rw [← h1, ← h2, hMid]

/-- Product `SimpleEquiv` across all `(chain i, step k)`: acts as the identity on the opened step
    `k.val = (digits i).val` and shifts `y₁ i k ↦ y₂ i k` at every unopened step `k.val ≠ (digits i).val`
    (including **every unopened earlier preimage position `k < d_i`**!). -/
def preSteppedPrefixRebalanceEquiv {R : Type} [LawfulCommRing R]
    (inv : R → R) (d L : Nat) (corruptPts : List R)
    (digits : Fin L → Fin 4)
    (y₁ y₂ : PreSteppedChainSecrets R L)
    (hCard : corruptPts.length + 1 ≤ d + 1) :
    SimpleEquiv (PreSteppedShamirTape R d L) (PreSteppedShamirTape R d L) where
  toFun tape i k :=
    if k.val = (digits i).val then
      tape i k
    else
      (shamirSecretShiftEquiv inv d corruptPts (y₁ i k) (y₂ i k) hCard).toFun (tape i k)
  invFun tape i k :=
    if k.val = (digits i).val then
      tape i k
    else
      (shamirSecretShiftEquiv inv d corruptPts (y₁ i k) (y₂ i k) hCard).invFun (tape i k)
  left_inv tape := by
    funext i k
    by_cases hk : k.val = (digits i).val
    · simp only [hk, ↓reduceIte]
    · simp only [hk, ↓reduceIte,
        (shamirSecretShiftEquiv inv d corruptPts (y₁ i k) (y₂ i k) hCard).left_inv]
  right_inv tape := by
    funext i k
    by_cases hk : k.val = (digits i).val
    · simp only [hk, ↓reduceIte]
    · simp only [hk, ↓reduceIte,
        (shamirSecretShiftEquiv inv d corruptPts (y₁ i k) (y₂ i k) hCard).right_inv]

/-- **Crown Jewel 3A — Exact `(t - 1)`-Collusion Zero-Knowledge for Unopened Chain Prefixes
    (`preStepped_shamir_unopened_prefix_zero_knowledge`)**:
    For ANY finite commutative ring/field `R` (`Goldilocks`, `TowerElem k`, etc.), threshold
    `t = d + 1`, corrupt set `corruptPts` of size `≤ t - 1` (`corruptPts.length + 1 ≤ d + 1`),
    digit vector `digits : Fin L → Fin 4`, and ANY two chain secret tables `y₁, y₂` agreeing ONLY
    on the opened step (`∀ i k, k.val = (digits i).val → y₁ i k = y₂ i k` — so all unopened
    preimage positions `k < d_i`, such as `y_i^(0)` and `y_i^(1)` when opening `y_i^(2)`, are
    completely unconstrained!):
    1. `preSteppedPrefixRebalanceEquiv` maps `y₁`-tapes bijectively onto `y₂`-tapes with **exact
       pointwise equality** of `computePreSteppedAdvView`;
    2. Over ANY finite enumeration `SimpleEquiv (Fin Card) (PreSteppedShamirTape R d L)` and ANY
       distinguisher `D : PreSteppedAdvView R L → Bool`, `finSum` counts are **identically equal**
       (`0` bits leaked about `y_i^(0)` and `y_i^(1)`!). -/
theorem preStepped_shamir_unopened_prefix_zero_knowledge {R : Type} [LawfulCommRing R]
    (inv : R → R) (hInv : ∀ x : R, x ≠ CommRingOps.zero → CommRingOps.mul x (inv x) = CommRingOps.one)
    (d L : Nat) (corruptPts : List R)
    (hCard : corruptPts.length + 1 ≤ d + 1)
    (hNonZero : ∀ c ∈ corruptPts, c ≠ CommRingOps.zero)
    (digits : Fin L → Fin 4)
    (y₁ y₂ : PreSteppedChainSecrets R L)
    (hOpenedAgree : ∀ (i : Fin L) (k : Fin 3), k.val = (digits i).val → y₁ i k = y₂ i k) :
    let bij := preSteppedPrefixRebalanceEquiv inv d L corruptPts digits y₁ y₂ hCard
    (∀ tape : PreSteppedShamirTape R d L,
      computePreSteppedAdvView corruptPts digits y₂ (bij.toFun tape) =
        computePreSteppedAdvView corruptPts digits y₁ tape) ∧
    (∀ (Card : Nat) (enum : SimpleEquiv (Fin Card) (PreSteppedShamirTape R d L))
       (D : PreSteppedAdvView R L → Bool),
      finSum Card (fun r => if D (computePreSteppedAdvView corruptPts digits y₁ (enum.toFun r)) then 1 else 0) =
        finSum Card (fun r => if D (computePreSteppedAdvView corruptPts digits y₂ (enum.toFun r)) then 1 else 0)) := by
  intro bij
  have hViewEq : ∀ tape : PreSteppedShamirTape R d L,
      computePreSteppedAdvView corruptPts digits y₂ (bij.toFun tape) =
        computePreSteppedAdvView corruptPts digits y₁ tape := by
    intro tape
    unfold computePreSteppedAdvView
    congr 1
    · funext i k
      dsimp only [bij, preSteppedPrefixRebalanceEquiv]
      by_cases hk : k.val = (digits i).val
      · simp only [hk, ↓reduceIte, hOpenedAgree i k hk]
      · simp only [hk, ↓reduceIte]
        exact List.map_congr_left
          (shamirSecretShiftEquiv_preserves_corruptShares inv hInv d corruptPts (y₁ i k) (y₂ i k)
            hCard hNonZero (tape i k))
    · funext i
      by_cases hd : (digits i).val < 3
      · simp only [hd, ↓reduceDIte]
        have hEqOpened := hOpenedAgree i ⟨(digits i).val, hd⟩ rfl
        dsimp only [bij, preSteppedPrefixRebalanceEquiv]
        simp only [↓reduceIte, hEqOpened]
      · simp only [hd, ↓reduceDIte]
  refine ⟨hViewEq, ?_⟩
  intro Card enum D
  let finBij : SimpleEquiv (Fin Card) (Fin Card) :=
    { toFun := fun r => enum.invFun (bij.toFun (enum.toFun r))
      invFun := fun r => enum.invFun (bij.invFun (enum.toFun r))
      left_inv := fun r => by rw [enum.right_inv, bij.left_inv, enum.left_inv]
      right_inv := fun r => by rw [enum.right_inv, bij.right_inv, enum.left_inv] }
  have hPerm := finSum_comp_simpleEquiv Card finBij
    (fun r => if D (computePreSteppedAdvView corruptPts digits y₂ (enum.toFun r)) then 1 else 0)
  rw [← hPerm]
  apply finSum_congr
  intro r
  dsimp only [finBij]
  rw [enum.right_inv, hViewEq (enum.toFun r)]

/-- **`#tooth` Reusing Polynomial Randomness Across Chain Steps Leaks Secret Key `y_i^(0)`
    (`tooth_shared_poly_across_chain_steps_leaks_preimage`)**:
    If the background table reuses the same random tail `A` for step `0` (`y₀ :: A`) and step `2`
    (`y₂ :: A`) instead of independent polynomials, then opening `y₂ :: A` online allows a SINGLE
    corrupt custodian at ANY point `xc` to recover the unopened chain secret `y₀` in 1 subtraction! -/
theorem tooth_shared_poly_across_chain_steps_leaks_preimage
    {R : Type} [LawfulCommRing R]
    (y₀ _y₂ xc : R) (A : List R) :
    let corruptShare₀ := RoundPoly.evalCoeffs (y₀ :: A) xc
    let openedTailFromStep2 := A
    CommRingOps.sub corruptShare₀ (CommRingOps.mul xc (RoundPoly.evalCoeffs openedTailFromStep2 xc)) = y₀ := by
  intro corruptShare₀ openedTailFromStep2
  change CommRingOps.sub (CommRingOps.add y₀ (CommRingOps.mul xc (RoundPoly.evalCoeffs A xc)))
    (CommRingOps.mul xc (RoundPoly.evalCoeffs A xc)) = y₀
  rw [LawfulCommRing.sub_eq_add_neg, LawfulCommRing.add_assoc,
      LawfulCommRing.add_right_neg, LawfulCommRing.add_zero]

/-! ### Crown Jewel 3B — MAC-Free Endpoint Self-Verification (`H^(3 - d_i)(reconstructed) = pk_i`) -/

/-- **`#tooth` Unverified Lagrange Interpolation Blindly Accepts Corrupted Shares
    (`tooth_unverified_lagrange_accepts_corrupted_share`)**:
    Without checking the chain endpoint `H^(3 - d_i)(cand) = pk_i`, linear Lagrange reconstruction
    `ringDot lambdas submitted` with non-zero weight `λ₀ ≠ 0` shifts the reconstructed output by
    `λ₀ · δ ≠ 0` whenever corrupt party `0` adds `δ ≠ 0` to its share! -/
theorem tooth_unverified_lagrange_accepts_corrupted_share
    {R : Type} [LawfulCommRing R] [NoZeroDivisors R]
    (lam₀ s₀ delta : R) (restLam restShares : List R)
    (hLamNz : lam₀ ≠ CommRingOps.zero) (hDeltaNz : delta ≠ CommRingOps.zero) :
    ringDot (lam₀ :: restLam) (CommRingOps.add s₀ delta :: restShares) ≠
      ringDot (lam₀ :: restLam) (s₀ :: restShares) := by
  simp only [ringDot, LawfulCommRing.left_distrib]
  intro hEq
  have hRearr :
      CommRingOps.add (CommRingOps.add (CommRingOps.mul lam₀ s₀) (CommRingOps.mul lam₀ delta))
        (ringDot restLam restShares) =
      CommRingOps.add (CommRingOps.add (CommRingOps.mul lam₀ s₀) (ringDot restLam restShares))
        (CommRingOps.mul lam₀ delta) := by
    rw [LawfulCommRing.add_assoc,
        LawfulCommRing.add_comm (CommRingOps.mul lam₀ delta) (ringDot restLam restShares),
        ← LawfulCommRing.add_assoc]
  rw [hRearr] at hEq
  have hZeroMul : CommRingOps.mul lam₀ delta = CommRingOps.zero := by
    apply LawfulCommRing.add_left_cancel
      (a := CommRingOps.add (CommRingOps.mul lam₀ s₀) (ringDot restLam restShares))
    rw [LawfulCommRing.add_zero]
    exact hEq
  rcases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero hZeroMul with h1 | h2
  · exact hLamNz h1
  · exact hDeltaNz h2

/-- Online MAC-free Lagrange reconstruction + `H^(3 - d_i)` endpoint self-verification across `L` chains. -/
def preSteppedReconstructAndSelfVerify {R : Type} [CommRingOps R] [DecidableEq R] {L : Nat}
    (F : Nat → Nat → R → R) (pk : Fin L → R)
    (lambdas : List R) (digits : Fin L → Fin 4)
    (submitted : Fin L → List R) : Option (Fin L → R) :=
  let cand : Fin L → R := fun i =>
    if (digits i).val < 3 then
      ringDot lambdas (submitted i)
    else
      pk i
  if (List.finRange L).all (fun i =>
      decide (wotsChainIter F i.val (digits i).val (3 - (digits i).val) (cand i) = pk i)) then
    some cand
  else
    none

private def extractChainMergeClaw {R : Type} [DecidableEq R]
    (F : Nat → Nat → R → R) (chainIdx : Nat) :
    (start rem : Nat) → (a b : R) →
    start + rem = 3 →
    a ≠ b →
    wotsChainIter F chainIdx start rem a = wotsChainIter F chainIdx start rem b →
    WotsChainCollisionWitness F 4
  | _, 0, _, _, _, hNe, hEq => False.elim (hNe hEq)
  | start, rem + 1, a, b, hBound, hNe, hEq =>
    if hStepEq : F chainIdx start a = F chainIdx start b then
      { chainIdx := chainIdx
        stepPos := start
        step_lt := by omega
        nodeA := a
        nodeB := b
        nodes_ne := hNe
        step_eq := hStepEq }
    else
      extractChainMergeClaw F chainIdx (start + 1) rem
        (F chainIdx start a) (F chainIdx start b) (by omega) hStepEq hEq

private def checkFinFnEq {R : Type} [DecidableEq R] :
    {L : Nat} → (f g : Fin L → R) → PSum (f = g) { i : Fin L // f i ≠ g i }
  | 0, _, _ => .inl (funext (fun i => Fin.elim0 i))
  | L + 1, f, g =>
    if h0 : f ⟨0, Nat.zero_lt_succ L⟩ = g ⟨0, Nat.zero_lt_succ L⟩ then
      match checkFinFnEq (fun j : Fin L => f ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩)
                         (fun j : Fin L => g ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩) with
      | .inl hTail =>
        .inl (funext (fun i => by
          cases i with
          | mk val isLt =>
            cases val with
            | zero => exact h0
            | succ k => exact congrFun hTail ⟨k, Nat.lt_of_succ_lt_succ isLt⟩))
      | .inr ⟨j, hj⟩ => .inr ⟨⟨j.1 + 1, Nat.succ_lt_succ j.2⟩, hj⟩
    else
      .inr ⟨⟨0, Nat.zero_lt_succ L⟩, h0⟩

/-- Constructive `PSum` extractor for MAC-free self-verification (`0 Classical.choice`):
    Given any `cand` accepted by `preSteppedReconstructAndSelfVerify`, returns EITHER `.inl` proving
    `cand = trueNodes` across all `L` chains, OR `.inr` exhibiting a concrete step collision/preimage
    in `F` (`WotsChainCollisionWitness F 4`)! -/
def extractPreSteppedSelfVerifyOutcome {R : Type} [LawfulCommRing R] [DecidableEq R] {L : Nat}
    (F : Nat → Nat → R → R) (sk : Fin L → R)
    (lambdas : List R) (digits : Fin L → Fin 4)
    (submitted : Fin L → List R) (cand : Fin L → R)
    (hAccepted :
      preSteppedReconstructAndSelfVerify F (fun i => wotsChainIter F i.val 0 3 (sk i))
        lambdas digits submitted = some cand) :
    let trueNodes : Fin L → R := fun i => wotsChainIter F i.val 0 (digits i).val (sk i)
    PSum (cand = trueNodes) (WotsChainCollisionWitness F 4) :=
  let pk : Fin L → R := fun i => wotsChainIter F i.val 0 3 (sk i)
  let trueNodes : Fin L → R := fun i => wotsChainIter F i.val 0 (digits i).val (sk i)
  match checkFinFnEq cand trueNodes with
  | .inl hEq => .inl hEq
  | .inr ⟨i, hiNe⟩ =>
    have hAllChecks :
        ((List.finRange L).all (fun j =>
          decide (wotsChainIter F j.val (digits j).val (3 - (digits j).val) (cand j) = pk j))) = true := by
      unfold preSteppedReconstructAndSelfVerify at hAccepted
      dsimp only at hAccepted
      split at hAccepted
      · rename_i hAll
        injection hAccepted with hCand
        rw [← hCand]
        exact hAll
      · cases hAccepted
    have hCandEndsAtPk : wotsChainIter F i.val (digits i).val (3 - (digits i).val) (cand i) = pk i :=
      of_decide_eq_true (List.all_eq_true.mp hAllChecks i (mem_finRange_self i))
    have _hDiLe3 : (digits i).val ≤ 3 := by have := (digits i).isLt; omega
    have hTrueEndsAtPk : wotsChainIter F i.val (digits i).val (3 - (digits i).val) (trueNodes i) = pk i := by
      dsimp only [trueNodes, pk]
      have hAdd : (digits i).val + (3 - (digits i).val) = 3 := by omega
      have hComp := wotsChainIter_add F i.val 0 (digits i).val (3 - (digits i).val) (sk i)
      simp only [Nat.zero_add, hAdd] at hComp
      exact hComp.symm
    .inr (extractChainMergeClaw F i.val (digits i).val (3 - (digits i).val)
            (cand i) (trueNodes i) (by omega) hiNe (hCandEndsAtPk.trans hTrueEndsAtPk.symm))

/-- **Crown Jewel 3B — MAC-Free Self-Verifying `(t, n)` Shamir `WOTS+C` Reconstruction
    (`preStepped_shamir_mac_free_self_verification`)**:
    1. **Honest Completeness (`0` MACs)**: When `t` parties at `pts` submit honest Shamir shares
       from the pre-stepped table `(trueNodes i :: (tape i d_i).1)` with Vandermonde-at-zero
       Lagrange weights `lambdas`, `preSteppedReconstructAndSelfVerify` deterministically outputs
       `some trueNodes`!
    2. **Adversarial Share-Corruption Soundness**: For ANY adversarially corrupted share vector
       `submitted'`, `preSteppedReconstructAndSelfVerify` EITHER rejects (`none`), returns the exact
       honest chain vector `some trueNodes`, OR constructively yields an explicit hash step
       collision/preimage `WotsChainCollisionWitness F 4` (`stepPos < 3`, `nodeA ≠ nodeB`,
       `F chainIdx stepPos nodeA = F chainIdx stepPos nodeB`)! -/
theorem preStepped_shamir_mac_free_self_verification
    {R : Type} [LawfulCommRing R] [DecidableEq R] {d L : Nat}
    (F : Nat → Nat → R → R) (sk : Fin L → R)
    (tape : PreSteppedShamirTape R d L)
    (lambdas pts : List R)
    (hZero : ringDot lambdas (pts.map (fun _ => CommRingOps.one)) = CommRingOps.one)
    (hHigher : ∀ deg, 1 ≤ deg → deg < d + 1 →
      ringDot lambdas (pts.map (fun x => ringPow x deg)) = CommRingOps.zero)
    (digits : Fin L → Fin 4) :
    let pk : Fin L → R := fun i => wotsChainIter F i.val 0 3 (sk i)
    let trueNodes : Fin L → R := fun i => wotsChainIter F i.val 0 (digits i).val (sk i)
    let honestSubmitted : Fin L → List R := fun i =>
      if h : (digits i).val < 3 then
        pts.map (fun x => RoundPoly.evalCoeffs (trueNodes i :: (tape i ⟨(digits i).val, h⟩).1) x)
      else
        []
    -- (1) Honest completeness:
    preSteppedReconstructAndSelfVerify F pk lambdas digits honestSubmitted = some trueNodes ∧
    -- (2) MAC-free self-verification soundness against arbitrary share corruption:
    (∀ (submitted' : Fin L → List R) (cand : Fin L → R),
      preSteppedReconstructAndSelfVerify F pk lambdas digits submitted' = some cand →
      cand = trueNodes ∨ Nonempty (WotsChainCollisionWitness F 4)) := by
  intro pk trueNodes honestSubmitted
  refine ⟨?_, ?_⟩
  · -- Part 1: Honest completeness
    have hCandEq :
        (fun i : Fin L =>
          if (digits i).val < 3 then ringDot lambdas (honestSubmitted i) else pk i) =
        trueNodes := by
      funext i
      by_cases hd : (digits i).val < 3
      · simp only [hd, ↓reduceIte, honestSubmitted, ↓reduceDIte]
        have hLen : (trueNodes i :: (tape i ⟨(digits i).val, hd⟩).1).length ≤ d + 1 := by
          simp [(tape i ⟨(digits i).val, hd⟩).2]
        rw [lagrangeAtZero_evalCoeffs lambdas pts _ (d + 1) hLen hZero hHigher]
        simp [LawfulCommRing.zero_mul, LawfulCommRing.add_zero]
      · have hdEq3 : (digits i).val = 3 := by have := (digits i).isLt; omega
        simp only [hd, ↓reduceIte]
        dsimp only [pk, trueNodes]
        rw [hdEq3]
    unfold preSteppedReconstructAndSelfVerify
    dsimp only
    have hEval : ∀ (c : Fin L → R), c = trueNodes →
        (if (List.finRange L).all (fun i =>
            decide (wotsChainIter F i.val (digits i).val (3 - (digits i).val) (c i) = pk i))
         then some c else none) = some trueNodes := by
      rintro c rfl
      have hAllOk :
          ((List.finRange L).all (fun i =>
            decide (wotsChainIter F i.val (digits i).val (3 - (digits i).val) (trueNodes i) = pk i))) = true := by
        apply List.all_eq_true.mpr
        intro i _
        apply decide_eq_true
        dsimp only [trueNodes, pk]
        have _hdLe3 : (digits i).val ≤ 3 := by have := (digits i).isLt; omega
        have hAdd : (digits i).val + (3 - (digits i).val) = 3 := by omega
        have hComp := wotsChainIter_add F i.val 0 (digits i).val (3 - (digits i).val) (sk i)
        simp only [Nat.zero_add, hAdd] at hComp
        exact hComp.symm
      rw [hAllOk]
      rfl
    exact hEval _ hCandEq
  · -- Part 2: Soundness via constructive extractor
    intro submitted' cand hAcc
    cases extractPreSteppedSelfVerifyOutcome F sk lambdas digits submitted' cand hAcc with
    | inl hEq => exact .inl hEq
    | inr w => exact .inr ⟨w⟩

/-! ### Crown Jewel 3C — Full 128-Bit `TowerElem 7` (`GF(2^128)`) Shamir Sharing of 256-Bit `Digest256` Chains (`v = 128`, `S = 192`) -/

/-- Split a 256-bit `Digest256` chain value into two 128-bit `TowerElem 7` (`GF(2^128)`) halves
    (`quorum_jorts.rs:580-615`). -/
def splitDigest256Tower128 (d : Digest256) : TowerElem 7 × TowerElem 7 :=
  unpackTower 8 d

/-- Reassemble two 128-bit `TowerElem 7` (`GF(2^128)`) halves into a 256-bit `Digest256`. -/
def joinTower128Digest256 (p : TowerElem 7 × TowerElem 7) : Digest256 :=
  packTower 8 p

@[simp] theorem join_splitDigest256Tower128 (d : Digest256) :
    joinTower128Digest256 (splitDigest256Tower128 d) = d :=
  packTower_unpackTower 8 d

@[simp] theorem split_joinTower128Digest256 (p : TowerElem 7 × TowerElem 7) :
    splitDigest256Tower128 (joinTower128Digest256 p) = p :=
  unpackTower_packTower 8 p

theorem joinTower128Digest256_injective {p₁ p₂ : TowerElem 7 × TowerElem 7}
    (h : joinTower128Digest256 p₁ = joinTower128Digest256 p₂) : p₁ = p₂ :=
  packTower_injective 8 p₁ p₂ h

/-- Top-level generator `towerX 7 ∈ GF(2^128)` lies **strictly outside** the 64-bit subfield
    `embedTower 6 (GF(2^64))`, ruling out embedded-subfield cosplay. -/
theorem towerX7_not_in_gf2_64 :
    ∀ sub : TowerElem 6, towerX 7 ≠ embedTower 6 sub := by
  intro sub hEq
  have hSnd : towerOne 6 = towerZero 6 := congrArg Prod.snd hEq
  exact towerOne_ne_zero 6 hSnd

theorem towerOne_ne_towerX (k : Nat) : towerOne (k + 1) ≠ towerX (k + 1) := by
  intro hEq
  exact towerOne_ne_zero k (congrArg Prod.fst hEq)

/-- Exact 2-point Lagrange weights at zero `[x₁ · (x₀ + x₁)⁻¹, x₀ · (x₀ + x₁)⁻¹]` over `TowerElem k`. -/
def lagrange2WeightsTower (k : Nat) (x₀ x₁ : TowerElem k) : List (TowerElem k) :=
  let denom := towerInv k (towerAdd k x₀ x₁)
  [towerMul k x₁ denom, towerMul k x₀ denom]

/-- Symbolic 2-point Lagrange interpolation theorem over `TowerElem k` (including `k = 7`, `GF(2^128)`):
    reconstructs `c₀` for ANY distinct `x₀ ≠ x₁` and ANY degree-`≤ 1` Shamir polynomial `c₀ :: tail.1`
    with zero WHNF unfolding of recursive norm inversion. -/
theorem lagrange2WeightsTower_eval (k : Nat) {x₀ x₁ : TowerElem k} (hNe : x₀ ≠ x₁)
    (c₀ : TowerElem k) (tail : ShamirPadPoly (TowerElem k) 1) :
    ringDot (lagrange2WeightsTower k x₀ x₁)
      ([x₀, x₁].map (fun x => RoundPoly.evalCoeffs (c₀ :: tail.1) x)) = c₀ := by
  rcases tail with ⟨cs, hLen⟩
  cases cs with
  | nil => cases hLen
  | cons c₁ rest =>
    cases rest with
    | cons _ _ => cases Nat.succ.inj hLen
    | nil =>
      have hSumNz : towerAdd k x₀ x₁ ≠ towerZero k := by
        intro hZ
        apply hNe
        calc x₀ = towerAdd k x₀ (towerZero k) := (towerAdd_zero k x₀).symm
          _ = towerAdd k x₀ (towerAdd k x₀ x₁) := by rw [hZ]
          _ = x₁ := towerAdd_cancel k x₀ x₁
      let denom := towerInv k (towerAdd k x₀ x₁)
      have hInvOk : towerMul k (towerAdd k x₀ x₁) denom = towerOne k :=
        towerMul_inv k (towerAdd k x₀ x₁) hSumNz
      dsimp only [lagrange2WeightsTower, List.map, ringDot, RoundPoly.evalCoeffs, CommRingOps.add,
        CommRingOps.mul, CommRingOps.zero]
      simp only [towerMul_zero, towerAdd_zero]
      rw [towerMul_add_distrib, towerMul_add_distrib]
      have hSlopeCancel :
          towerMul k (towerMul k x₁ denom) (towerMul k x₀ c₁) =
          towerMul k (towerMul k x₀ denom) (towerMul k x₁ c₁) := by
        calc towerMul k (towerMul k x₁ denom) (towerMul k x₀ c₁)
            = towerMul k (towerMul k denom x₁) (towerMul k x₀ c₁) := by rw [towerMul_comm k x₁ denom]
          _ = towerMul k denom (towerMul k x₁ (towerMul k x₀ c₁)) := towerMul_assoc k denom x₁ _
          _ = towerMul k denom (towerMul k (towerMul k x₁ x₀) c₁) := by rw [← towerMul_assoc k x₁ x₀ c₁]
          _ = towerMul k denom (towerMul k (towerMul k x₀ x₁) c₁) := by rw [towerMul_comm k x₁ x₀]
          _ = towerMul k denom (towerMul k x₀ (towerMul k x₁ c₁)) := by rw [towerMul_assoc k x₀ x₁ c₁]
          _ = towerMul k (towerMul k denom x₀) (towerMul k x₁ c₁) := (towerMul_assoc k denom x₀ _).symm
          _ = towerMul k (towerMul k x₀ denom) (towerMul k x₁ c₁) := by rw [towerMul_comm k denom x₀]
      have h4 : ∀ (a b c d : TowerElem k),
          towerAdd k (towerAdd k a b) (towerAdd k c d) =
          towerAdd k (towerAdd k a c) (towerAdd k b d) := fun a b c d => by
        calc towerAdd k (towerAdd k a b) (towerAdd k c d)
            = towerAdd k a (towerAdd k b (towerAdd k c d)) := towerAdd_assoc k a b _
          _ = towerAdd k a (towerAdd k (towerAdd k b c) d) := by rw [← towerAdd_assoc k b c d]
          _ = towerAdd k a (towerAdd k (towerAdd k c b) d) := by rw [towerAdd_comm k b c]
          _ = towerAdd k a (towerAdd k c (towerAdd k b d)) := by rw [towerAdd_assoc k c b d]
          _ = towerAdd k (towerAdd k a c) (towerAdd k b d) := (towerAdd_assoc k a c _).symm
      rw [h4, hSlopeCancel, towerAdd_self_zero, towerAdd_zero]
      calc towerAdd k (towerMul k (towerMul k x₁ denom) c₀) (towerMul k (towerMul k x₀ denom) c₀)
          = towerMul k (towerAdd k (towerMul k x₁ denom) (towerMul k x₀ denom)) c₀ :=
              (towerAdd_mul_distrib k _ _ c₀).symm
        _ = towerMul k (towerMul k (towerAdd k x₁ x₀) denom) c₀ := by
              rw [← towerAdd_mul_distrib k x₁ x₀ denom]
        _ = towerMul k (towerMul k (towerAdd k x₀ x₁) denom) c₀ := by
              rw [towerAdd_comm k x₁ x₀]
        _ = towerMul k (towerOne k) c₀ := by rw [hInvOk]
        _ = c₀ := towerOne_mul k c₀

theorem lagrange2HeadWeight_ne_zero (k : Nat) {x₀ x₁ : TowerElem k}
    (hNe : x₀ ≠ x₁) (hx₁Nz : x₁ ≠ towerZero k) :
    towerMul k x₁ (towerInv k (towerAdd k x₀ x₁)) ≠ towerZero k := by
  have hSumNz : towerAdd k x₀ x₁ ≠ towerZero k := by
    intro hZ
    apply hNe
    calc x₀ = towerAdd k x₀ (towerZero k) := (towerAdd_zero k x₀).symm
      _ = towerAdd k x₀ (towerAdd k x₀ x₁) := by rw [hZ]
      _ = x₁ := towerAdd_cancel k x₀ x₁
  have hDenomNz : towerInv k (towerAdd k x₀ x₁) ≠ towerZero k := by
    intro hDz
    have hInv := towerMul_inv k (towerAdd k x₀ x₁) hSumNz
    rw [hDz, towerMul_zero] at hInv
    exact towerOne_ne_zero k hInv.symm
  intro hProdZ
  rcases (towerMul_eq_zero_iff k x₁ _).mp hProdZ with h1 | h2
  · exact hx₁Nz h1
  · exact hDenomNz h2

/-- Secret intermediate 256-bit `Digest256` chain positions `(y_i^(0), y_i^(1), y_i^(2))` across `L` chains. -/
abbrev PreSteppedDigest256Secrets (L : Nat) := Fin L → Fin 3 → Digest256

/-- Paired degree-`≤ d` `TowerElem 7` (`GF(2^128)`) Shamir polynomials per 256-bit `(chain i, step k)`. -/
abbrev PreSteppedDigest256ShamirTape (d L : Nat) :=
  Fin L → Fin 3 → ShamirPadPoly (TowerElem 7) d × ShamirPadPoly (TowerElem 7) d

/-- Adversary `(t - 1)`-collusion view for 256-bit `Digest256` chains shared over `TowerElem 7` (`GF(2^128)`). -/
structure PreSteppedDigest256AdvView (L : Nat) where
  corruptTableShares : Fin L → Fin 3 → List (TowerElem 7) × List (TowerElem 7)
  onlineOpenedPolys : Fin L → Option (List (TowerElem 7) × List (TowerElem 7))

/-- Compute the `GF(2^128)²` `(t - 1)`-collusion adversary view from 256-bit chain secrets `y`. -/
def computePreSteppedDigest256AdvView {d L : Nat}
    (corruptPts : List (TowerElem 7)) (digits : Fin L → Fin 4)
    (y : PreSteppedDigest256Secrets L) (tape : PreSteppedDigest256ShamirTape d L) :
    PreSteppedDigest256AdvView L where
  corruptTableShares i k :=
    let (lo, hi) := splitDigest256Tower128 (y i k)
    (corruptPts.map (fun xc => RoundPoly.evalCoeffs (lo :: (tape i k).1.1) xc),
     corruptPts.map (fun xc => RoundPoly.evalCoeffs (hi :: (tape i k).2.1) xc))
  onlineOpenedPolys i :=
    if h : (digits i).val < 3 then
      let k : Fin 3 := ⟨(digits i).val, h⟩
      let (lo, hi) := splitDigest256Tower128 (y i k)
      some (lo :: (tape i k).1.1, hi :: (tape i k).2.1)
    else
      none

/-- Product `SimpleEquiv` shifting both `GF(2^128)` halves of every unopened 256-bit chain step (`0 Classical.choice`). -/
def preSteppedDigest256RebalanceEquiv (d L : Nat)
    (corruptPts : List (TowerElem 7)) (digits : Fin L → Fin 4)
    (y₁ y₂ : PreSteppedDigest256Secrets L)
    (hCard : corruptPts.length + 1 ≤ d + 1) :
    SimpleEquiv (PreSteppedDigest256ShamirTape d L) (PreSteppedDigest256ShamirTape d L) where
  toFun tape i k :=
    if k.val = (digits i).val then
      tape i k
    else
      let (lo₁, hi₁) := splitDigest256Tower128 (y₁ i k)
      let (lo₂, hi₂) := splitDigest256Tower128 (y₂ i k)
      ((shamirSecretShiftEquiv (towerInv 7) d corruptPts lo₁ lo₂ hCard).toFun (tape i k).1,
       (shamirSecretShiftEquiv (towerInv 7) d corruptPts hi₁ hi₂ hCard).toFun (tape i k).2)
  invFun tape i k :=
    if k.val = (digits i).val then
      tape i k
    else
      let (lo₁, hi₁) := splitDigest256Tower128 (y₁ i k)
      let (lo₂, hi₂) := splitDigest256Tower128 (y₂ i k)
      ((shamirSecretShiftEquiv (towerInv 7) d corruptPts lo₁ lo₂ hCard).invFun (tape i k).1,
       (shamirSecretShiftEquiv (towerInv 7) d corruptPts hi₁ hi₂ hCard).invFun (tape i k).2)
  left_inv tape := by
    funext i k
    by_cases hk : k.val = (digits i).val
    · simp only [hk, ↓reduceIte]
    · simp only [hk, ↓reduceIte]
      rcases tape i k with ⟨tLo, tHi⟩
      simp only [(shamirSecretShiftEquiv (towerInv 7) d corruptPts _ _ hCard).left_inv]
  right_inv tape := by
    funext i k
    by_cases hk : k.val = (digits i).val
    · simp only [hk, ↓reduceIte]
    · simp only [hk, ↓reduceIte]
      rcases tape i k with ⟨tLo, tHi⟩
      simp only [(shamirSecretShiftEquiv (towerInv 7) d corruptPts _ _ hCard).right_inv]

/-- **Full `TowerElem 7` (`GF(2^128)`) Zero-Knowledge for Unopened 256-Bit `Digest256` Chain Prefixes
    (`preStepped_tower128_digest256_zero_knowledge`)**:
    Over `TowerElem 7` (`GF(2^128)`) across `L` (e.g. `v = 128`) 256-bit `Digest256` chains, up to
    `t - 1` corrupt evaluation points `corruptPts` learn **exact `0` bits** (`0` statistical distance
    in `finSum`) about every unopened 256-bit preimage `y_i^(k)` (`k ≠ d_i`)! -/
theorem preStepped_tower128_digest256_zero_knowledge
    (d L : Nat) (corruptPts : List (TowerElem 7))
    (hCard : corruptPts.length + 1 ≤ d + 1)
    (hNonZero : ∀ c ∈ corruptPts, c ≠ towerZero 7)
    (digits : Fin L → Fin 4)
    (y₁ y₂ : PreSteppedDigest256Secrets L)
    (hOpenedAgree : ∀ (i : Fin L) (k : Fin 3), k.val = (digits i).val → y₁ i k = y₂ i k) :
    let bij := preSteppedDigest256RebalanceEquiv d L corruptPts digits y₁ y₂ hCard
    (∀ tape : PreSteppedDigest256ShamirTape d L,
      computePreSteppedDigest256AdvView corruptPts digits y₂ (bij.toFun tape) =
        computePreSteppedDigest256AdvView corruptPts digits y₁ tape) ∧
    (∀ (Card : Nat) (enum : SimpleEquiv (Fin Card) (PreSteppedDigest256ShamirTape d L))
       (D : PreSteppedDigest256AdvView L → Bool),
      finSum Card (fun r => if D (computePreSteppedDigest256AdvView corruptPts digits y₁ (enum.toFun r)) then 1 else 0) =
        finSum Card (fun r => if D (computePreSteppedDigest256AdvView corruptPts digits y₂ (enum.toFun r)) then 1 else 0)) := by
  intro bij
  have hInv7 : ∀ x : TowerElem 7, x ≠ CommRingOps.zero →
      CommRingOps.mul x (towerInv 7 x) = CommRingOps.one :=
    fun x hx => towerMul_inv 7 x hx
  have hViewEq : ∀ tape : PreSteppedDigest256ShamirTape d L,
      computePreSteppedDigest256AdvView corruptPts digits y₂ (bij.toFun tape) =
        computePreSteppedDigest256AdvView corruptPts digits y₁ tape := by
    intro tape
    unfold computePreSteppedDigest256AdvView
    congr 1
    · funext i k
      dsimp only [bij, preSteppedDigest256RebalanceEquiv]
      by_cases hk : k.val = (digits i).val
      · simp only [hk, ↓reduceIte, hOpenedAgree i k hk]
      · simp only [hk, ↓reduceIte]
        apply Prod.ext
        · exact List.map_congr_left
            (shamirSecretShiftEquiv_preserves_corruptShares (towerInv 7) hInv7 d corruptPts
              (splitDigest256Tower128 (y₁ i k)).1 (splitDigest256Tower128 (y₂ i k)).1
              hCard hNonZero (tape i k).1)
        · exact List.map_congr_left
            (shamirSecretShiftEquiv_preserves_corruptShares (towerInv 7) hInv7 d corruptPts
              (splitDigest256Tower128 (y₁ i k)).2 (splitDigest256Tower128 (y₂ i k)).2
              hCard hNonZero (tape i k).2)
    · funext i
      by_cases hd : (digits i).val < 3
      · simp only [hd, ↓reduceDIte]
        have hEqOpened := hOpenedAgree i ⟨(digits i).val, hd⟩ rfl
        dsimp only [bij, preSteppedDigest256RebalanceEquiv]
        simp only [↓reduceIte, hEqOpened]
      · simp only [hd, ↓reduceDIte]
  refine ⟨hViewEq, ?_⟩
  intro Card enum D
  let finBij : SimpleEquiv (Fin Card) (Fin Card) :=
    { toFun := fun r => enum.invFun (bij.toFun (enum.toFun r))
      invFun := fun r => enum.invFun (bij.invFun (enum.toFun r))
      left_inv := fun r => by rw [enum.right_inv, bij.left_inv, enum.left_inv]
      right_inv := fun r => by rw [enum.right_inv, bij.right_inv, enum.left_inv] }
  have hPerm := finSum_comp_simpleEquiv Card finBij
    (fun r => if D (computePreSteppedDigest256AdvView corruptPts digits y₂ (enum.toFun r)) then 1 else 0)
  rw [← hPerm]
  apply finSum_congr
  intro r
  dsimp only [finBij]
  rw [enum.right_inv, hViewEq (enum.toFun r)]

/-- Online `GF(2^128)²` (`TowerElem 7`) Shamir shares submitted per 256-bit chain. -/
abbrev SubmittedDigest256ShamirShares (L : Nat) :=
  Fin L → List (TowerElem 7) × List (TowerElem 7)

/-- Online MAC-free `TowerElem 7` (`GF(2^128)`) Lagrange reconstruction + 256-bit `Digest256`
    endpoint self-verification (`wotsChainIter F i d_i (3 - d_i) (cand i) = pk i`) across `L` chains
    (`quorum_jorts.rs:605-642`). -/
def preSteppedDigest256ReconstructAndSelfVerify {L : Nat}
    (F : Nat → Nat → Digest256 → Digest256) (pk : Fin L → Digest256)
    (lambdas : List (TowerElem 7)) (digits : Fin L → Fin 4)
    (submitted : SubmittedDigest256ShamirShares L) : Option (Fin L → Digest256) :=
  let cand : Fin L → Digest256 := fun i =>
    if (digits i).val < 3 then
      joinTower128Digest256
        (ringDot lambdas (submitted i).1, ringDot lambdas (submitted i).2)
    else
      pk i
  if (List.finRange L).all (fun i =>
      decide (wotsChainIter F i.val (digits i).val (3 - (digits i).val) (cand i) = pk i)) then
    some cand
  else
    none

/-- Constructive `PSum` extractor for 256-bit `Digest256` self-verification over `TowerElem 7` (`0 Classical.choice`). -/
def extractPreSteppedDigest256Outcome {L : Nat}
    (F : Nat → Nat → Digest256 → Digest256) (sk : Fin L → Digest256)
    (lambdas : List (TowerElem 7)) (digits : Fin L → Fin 4)
    (submitted : SubmittedDigest256ShamirShares L) (cand : Fin L → Digest256)
    (hAccepted :
      preSteppedDigest256ReconstructAndSelfVerify F (fun i => wotsChainIter F i.val 0 3 (sk i))
        lambdas digits submitted = some cand) :
    let trueNodes : Fin L → Digest256 := fun i => wotsChainIter F i.val 0 (digits i).val (sk i)
    PSum (cand = trueNodes) (WotsChainCollisionWitness F 4) :=
  let pk : Fin L → Digest256 := fun i => wotsChainIter F i.val 0 3 (sk i)
  let trueNodes : Fin L → Digest256 := fun i => wotsChainIter F i.val 0 (digits i).val (sk i)
  match checkFinFnEq cand trueNodes with
  | .inl hEq => .inl hEq
  | .inr ⟨i, hiNe⟩ =>
    have hAllChecks :
        ((List.finRange L).all (fun j =>
          decide (wotsChainIter F j.val (digits j).val (3 - (digits j).val) (cand j) = pk j))) = true := by
      unfold preSteppedDigest256ReconstructAndSelfVerify at hAccepted
      dsimp only at hAccepted
      split at hAccepted
      · rename_i hAll
        injection hAccepted with hCand
        rw [← hCand]
        exact hAll
      · cases hAccepted
    have hCandEndsAtPk : wotsChainIter F i.val (digits i).val (3 - (digits i).val) (cand i) = pk i :=
      of_decide_eq_true (List.all_eq_true.mp hAllChecks i (mem_finRange_self i))
    have _hDiLe3 : (digits i).val ≤ 3 := by have := (digits i).isLt; omega
    have hTrueEndsAtPk : wotsChainIter F i.val (digits i).val (3 - (digits i).val) (trueNodes i) = pk i := by
      dsimp only [trueNodes, pk]
      have hAdd : (digits i).val + (3 - (digits i).val) = 3 := by omega
      have hComp := wotsChainIter_add F i.val 0 (digits i).val (3 - (digits i).val) (sk i)
      simp only [Nat.zero_add, hAdd] at hComp
      exact hComp.symm
    .inr (extractChainMergeClaw F i.val (digits i).val (3 - (digits i).val)
            (cand i) (trueNodes i) (by omega) hiNe (hCandEndsAtPk.trans hTrueEndsAtPk.symm))

/-- **Full `TowerElem 7` (`GF(2^128)`) MAC-Free Self-Verifying 256-Bit `Digest256` `WOTS+C` Theorem
    (`preStepped_tower128_digest256_self_verification`)**:
    Across `L` chains (specifically `v = 128`, `WOTS_TARGET_SUM = 192` in `QuorumJorts`):
    1. **Honest Completeness**: Honest `TowerElem 7` (`GF(2^128)`) Shamir shares of
       `splitDigest256Tower128 (trueNodes i)` reconstruct and pass 256-bit endpoint self-verification
       (`= some trueNodes`) with `0` MACs!
    2. **Adversarial Share-Corruption Soundness**: Any corrupted `GF(2^128)` share vector `submitted'`
       is EITHER rejected (`none`), yields `some trueNodes`, OR constructively yields an explicit
       256-bit hash step collision/preimage `WotsChainCollisionWitness F 4`! -/
theorem preStepped_tower128_digest256_self_verification {d L : Nat}
    (F : Nat → Nat → Digest256 → Digest256) (sk : Fin L → Digest256)
    (tape : PreSteppedDigest256ShamirTape d L)
    (lambdas pts : List (TowerElem 7))
    (hLagrange : ∀ (c₀ : TowerElem 7) (tail : ShamirPadPoly (TowerElem 7) d),
      ringDot lambdas (pts.map (fun x => RoundPoly.evalCoeffs (c₀ :: tail.1) x)) = c₀)
    (digits : Fin L → Fin 4) :
    let pk : Fin L → Digest256 := fun i => wotsChainIter F i.val 0 3 (sk i)
    let trueNodes : Fin L → Digest256 := fun i => wotsChainIter F i.val 0 (digits i).val (sk i)
    let honestSubmitted : SubmittedDigest256ShamirShares L := fun i =>
      if h : (digits i).val < 3 then
        let k : Fin 3 := ⟨(digits i).val, h⟩
        let (lo, hi) := splitDigest256Tower128 (trueNodes i)
        (pts.map (fun x => RoundPoly.evalCoeffs (lo :: (tape i k).1.1) x),
         pts.map (fun x => RoundPoly.evalCoeffs (hi :: (tape i k).2.1) x))
      else
        ([], [])
    preSteppedDigest256ReconstructAndSelfVerify F pk lambdas digits honestSubmitted = some trueNodes ∧
    (∀ (submitted' : SubmittedDigest256ShamirShares L) (cand : Fin L → Digest256),
      preSteppedDigest256ReconstructAndSelfVerify F pk lambdas digits submitted' = some cand →
      cand = trueNodes ∨ Nonempty (WotsChainCollisionWitness F 4)) := by
  intro pk trueNodes honestSubmitted
  refine ⟨?_, ?_⟩
  · have hCandEq :
        (fun i : Fin L =>
          if (digits i).val < 3 then
            joinTower128Digest256
              (ringDot lambdas (honestSubmitted i).1, ringDot lambdas (honestSubmitted i).2)
          else pk i) = trueNodes := by
      funext i
      by_cases hd : (digits i).val < 3
      · simp only [hd, ↓reduceIte, honestSubmitted, ↓reduceDIte]
        rw [hLagrange _ (tape i ⟨(digits i).val, hd⟩).1,
            hLagrange _ (tape i ⟨(digits i).val, hd⟩).2]
        exact join_splitDigest256Tower128 (trueNodes i)
      · have hdEq3 : (digits i).val = 3 := by have := (digits i).isLt; omega
        simp only [hd, ↓reduceIte]
        dsimp only [pk, trueNodes]
        rw [hdEq3]
    unfold preSteppedDigest256ReconstructAndSelfVerify
    dsimp only
    have hEval : ∀ (c : Fin L → Digest256), c = trueNodes →
        (if (List.finRange L).all (fun i =>
            decide (wotsChainIter F i.val (digits i).val (3 - (digits i).val) (c i) = pk i))
         then some c else none) = some trueNodes := by
      rintro c rfl
      have hAllOk :
          ((List.finRange L).all (fun i =>
            decide (wotsChainIter F i.val (digits i).val (3 - (digits i).val) (trueNodes i) = pk i))) = true := by
        apply List.all_eq_true.mpr
        intro i _
        apply decide_eq_true
        dsimp only [trueNodes, pk]
        have _hdLe3 : (digits i).val ≤ 3 := by have := (digits i).isLt; omega
        have hAdd : (digits i).val + (3 - (digits i).val) = 3 := by omega
        have hComp := wotsChainIter_add F i.val 0 (digits i).val (3 - (digits i).val) (sk i)
        simp only [Nat.zero_add, hAdd] at hComp
        exact hComp.symm
      rw [hAllOk]
      rfl
    exact hEval _ hCandEq
  · intro submitted' cand hAcc
    cases extractPreSteppedDigest256Outcome F sk lambdas digits submitted' cand hAcc with
    | inl hEq => exact .inl hEq
    | inr w => exact .inr ⟨w⟩

/-! ## §4. Explicit `inhabited_*` Non-Vacuity Witnesses & `SimulationSpine` Exports -/

/-- Compositional `SimulationSpine` `PartyMachine` packaging `beltLatchBindStep`. -/
def beltLatchPartyMachine : PartyMachine BeltLatchNodeState BeltLatchRecord BeltBindOutcome :=
  PartyMachine.ofCustodyStep beltLatchBindStep

/-- Inhabitedness witness 1 (`inhabited_beltLatch_quorum_network_3f_plus_1`):
    Concrete `(t = 3, n = 7, f = 2, q = 5)` multi-turn network trace executing fresh binds,
    Mode 3B leaf staging, pairwise-MAC echo broadcast across a 5-custodian quorum, a power-loss
    crash + WAL recovery + Mode 3A idempotent replay, and certified quorum share release! -/
theorem inhabited_beltLatch_quorum_network_3f_plus_1 :
    let H : List UInt8 → Digest256 := fun _ => 0xAA#256
    let MAC : Digest256 → List UInt8 → Digest256 := fun k _ => k
    let macKeys : Fin 7 → Fin 7 → Digest256 := fun _ _ => 0x55#256
    let Corrupt : CustodiansMask 7 := ⟨fun i => decide (i.val = 5 ∨ i.val = 6)⟩
    let Q : CustodiansMask 7 := ⟨fun i => decide (i.val < 5)⟩
    let rec₀ : BeltLatchRecord :=
      { epoch := 0, msgDigest := 0x11#256, retrySalt := 0x22#256, targetSumDigits := [1, 2, 0, 3] }
    let p0 : Fin 7 := ⟨0, by decide⟩
    let p1 : Fin 7 := ⟨1, by decide⟩
    let p2 : Fin 7 := ⟨2, by decide⟩
    let p3 : Fin 7 := ⟨3, by decide⟩
    let p4 : Fin 7 := ⟨4, by decide⟩
    let trace : List (BeltNetworkTurn 7) :=
      [ .stageMode3BLeaf p0 0,
        .honestBind p0 rec₀, .honestBind p1 rec₀, .honestBind p2 rec₀,
        .honestBind p3 rec₀, .honestBind p4 rec₀,
        .crashAndRecoverNode p0,
        .honestBind p0 rec₀,
        .honestEmitEcho p0 p0, .honestEmitEcho p1 p0, .honestEmitEcho p2 p0,
        .honestEmitEcho p3 p0, .honestEmitEcho p4 p0 ]
    let netMid := runBeltNetworkTrace H MAC macKeys Corrupt 5 (BeltLatchNetworkState.init 7 20 4) trace
    let netFinal := stepBeltNetwork H MAC macKeys Corrupt 5 netMid
      (.authorizeQuorumRelease p0 Q rec₀ netMid.emittedHonestEchoes)
    2 * 5 > 7 + 2 ∧
    maskCard Corrupt = 2 ∧
    maskCard Q = 5 ∧
    (netFinal.nodes p0).stagedWindow = [] ∧
    (Q, p0, rec₀) ∈ netFinal.certifiedReleases := by
  decide

/-- Inhabitedness witness 2 (`inhabited_committee_partitioned_jorts_2of3_and_3of5`):
    Multi-turn `(2, 3)` (`3` subtrees, `1` corrupt/offline) and `(3, 5)` (`10` subtrees, `2`
    corrupt/offline) executions over `List (QuorumJortsTurn 3)` and `List (QuorumJortsTurn 5)`
    advancing durable `BeltLatch` subtree cursors across consecutive epochs (`epoch = 0, 1`),
    emitting certified `ReleasedQuorumLeaf` signatures, and verifying `t`-of-`t` XOR reconstruction! -/
theorem inhabited_committee_partitioned_jorts_2of3_and_3of5 :
    let H : List UInt8 → Digest256 := fun _ => 0xAA#256
    let MAC : Digest256 → List UInt8 → Digest256 := fun k _ => k
    let macKeys3 : Fin 3 → Fin 3 → Digest256 := fun i j => BitVec.ofNat 256 (i.val + j.val + 1)
    let macKeys5 : Fin 5 → Fin 5 → Digest256 := fun i j => BitVec.ofNat 256 (i.val + j.val + 1)
    let C3 : CustodiansMask 3 := ⟨fun i => decide (i.val = 2)⟩
    let Online3 : CustodiansMask 3 := ⟨fun i => decide (i.val < 2)⟩
    let C5 : CustodiansMask 5 := ⟨fun i => decide (i.val = 3 ∨ i.val = 4)⟩
    let Online5 : CustodiansMask 5 := ⟨fun i => decide (i.val < 3)⟩
    let rec₀ : BeltLatchRecord :=
      { epoch := 0, msgDigest := 0x1010#256, retrySalt := 0x01#256, targetSumDigits := [2, 1] }
    let rec₁ : BeltLatchRecord :=
      { epoch := 1, msgDigest := 0x2020#256, retrySalt := 0x02#256, targetSumDigits := [1, 2] }
    let v3 : Fin 3 := ⟨0, by decide⟩
    let v5 : Fin 5 := ⟨0, by decide⟩
    let trace3 : List (QuorumJortsTurn 3) :=
      buildCommitteeSignTrace H MAC macKeys3 0 Online3 v3 rec₀ ++
      buildCommitteeSignTrace H MAC macKeys3 0 Online3 v3 rec₁
    let trace5 : List (QuorumJortsTurn 5) :=
      buildCommitteeSignTrace H MAC macKeys5 0 Online5 v5 rec₀ ++
      buildCommitteeSignTrace H MAC macKeys5 0 Online5 v5 rec₁
    let net3 := runQuorumJortsTrace H MAC macKeys3 C3 2 4 2 (QuorumJortsNetworkState.init 3 4 2) trace3
    let net5 := runQuorumJortsTrace H MAC macKeys5 C5 3 4 3 (QuorumJortsNetworkState.init 5 4 2) trace5
    let tape2 : Fin 1 → Digest256 := fun _ => 0xABCD#256
    let tape3 : Fin 2 → Digest256 := fun j => if j.val = 0 then 0x1234#256 else 0x5678#256
    (chooseMasks 3 2).length = 3 ∧
    (chooseMasks 5 3).length = 10 ∧
    2 ≤ maskCard (maskDiff Online3 C3) ∧
    3 ≤ maskCard (maskDiff Online5 C5) ∧
    net3.releasedLeaves.length = 2 ∧
    net5.releasedLeaves.length = 2 ∧
    (net3.slots v3 0).nextEpoch = 2 ∧
    (net5.slots v5 0).nextEpoch = 2 ∧
    xorFin256 2 (dealAdditiveShares 2 0xCAFE#256 tape2) = 0xCAFE#256 ∧
    xorFin256 3 (dealAdditiveShares 3 0xBEEF#256 tape3) = 0xBEEF#256 := by
  decide

private theorem preSteppedDigest256_accepted_component {L : Nat}
    (F : Nat → Nat → Digest256 → Digest256) (pk : Fin L → Digest256)
    (lambdas : List (TowerElem 7)) (digits : Fin L → Fin 4)
    (sub : SubmittedDigest256ShamirShares L) (cand : Fin L → Digest256)
    (i : Fin L) (hd : (digits i).val < 3)
    (accepted : preSteppedDigest256ReconstructAndSelfVerify F pk lambdas digits sub = some cand) :
    cand i = joinTower128Digest256 (ringDot lambdas (sub i).1, ringDot lambdas (sub i).2) := by
  unfold preSteppedDigest256ReconstructAndSelfVerify at accepted
  dsimp only at accepted
  split at accepted
  next =>
    have same := Option.some.inj accepted
    rw [← same]
    simp only [hd, ↓reduceIte]
  next => cases accepted

set_option maxHeartbeats 800000 in
/-- Inhabitedness witness 3 (`inhabited_preStepped_shamir_wots_self_verify`):
    Full 128-bit `TowerElem 7` (`GF(2^128)`) `(t = 2, n = 3)` pre-stepped Shamir `WOTS+C` table over
    256-bit `Digest256` chains across `v = 128` base-4 chains (`WOTS_TARGET_SUM = 192`, evaluation
    points `[towerOne 7, towerX 7]` with `towerX 7 ∉ GF(2^64)`):
    1. Verifies `validWotsCsCodeword 128 4 192` across all `128` chains (`64 × 2 + 64 × 1 = 192`);
    2. Proves honest `GF(2^128)` Shamir reconstruction + MAC-free endpoint self-verification on
       **real `quorumChainStep shake256Digest256`** (`= some trueShake`);
    3. Proves **`#tooth` corrupted-share rejection** when corrupt party `0` perturbs its `GF(2^128)`
       share on chain `0` by `towerX 7`: both soundness on `quorumChainStep shake256Digest256`
       (rejects `.isNone = true` or extracts a concrete `SHAKE256` chain collision) AND unconditional
       `.isNone = true` rejection on 256-bit `Digest256` chains across `Fin 128`! -/
theorem inhabited_preStepped_shamir_wots_self_verify :
    let pts : List (TowerElem 7) := [towerOne 7, towerX 7]
    let lambdas : List (TowerElem 7) := lagrange2WeightsTower 7 (towerOne 7) (towerX 7)
    let digits : Fin 128 → Fin 4 := fun i => if i.val < 64 then ⟨2, by decide⟩ else ⟨1, by decide⟩
    let digitsNat : List Nat := (List.finRange 128).map (fun i => (digits i).val)
    let tape : PreSteppedDigest256ShamirTape 1 128 :=
      fun _ _ => (⟨[towerX 7], rfl⟩, ⟨[towerOne 7], rfl⟩)
    let masterSeed : Digest256 := 0x0123456789ABCDEF0123456789ABCDEF0123456789ABCDEF0123456789ABCDEF#256
    let pkSeed : Digest256 := quorumStagePkSeed shake256Digest256 masterSeed
    let F_shake : Nat → Nat → Digest256 → Digest256 := quorumChainStep shake256Digest256 pkSeed 0
    let skShake : Fin 128 → Digest256 :=
      fun i => quorumStageChainSk shake256Digest256 masterSeed 0 (UInt32.ofNat i.val)
    let pkShake : Fin 128 → Digest256 := fun i => wotsChainIter F_shake i.val 0 3 (skShake i)
    let trueShake : Fin 128 → Digest256 := fun i => wotsChainIter F_shake i.val 0 (digits i).val (skShake i)
    let honestSubShake : SubmittedDigest256ShamirShares 128 := fun i =>
      if h : (digits i).val < 3 then
        let k : Fin 3 := ⟨(digits i).val, h⟩
        let (lo, hi) := splitDigest256Tower128 (trueShake i)
        (pts.map (fun x => RoundPoly.evalCoeffs (lo :: (tape i k).1.1) x),
         pts.map (fun x => RoundPoly.evalCoeffs (hi :: (tape i k).2.1) x))
      else ([], [])
    let corruptSubShake : SubmittedDigest256ShamirShares 128 := fun i =>
      if i.val = 0 then
        let (lo, hi) := splitDigest256Tower128 (trueShake i)
        ([towerAdd 7 (RoundPoly.evalCoeffs (lo :: [towerX 7]) (towerOne 7)) (towerX 7),
          RoundPoly.evalCoeffs (lo :: [towerX 7]) (towerX 7)],
         pts.map (fun x => RoundPoly.evalCoeffs (hi :: [towerOne 7]) x))
      else
        honestSubShake i
    let F_perm : Nat → Nat → Digest256 → Digest256 :=
      fun chain step x => x ^^^ BitVec.ofNat 256 (0x9E3779B97F4A7C15 + chain * 257 + step)
    let skPerm : Fin 128 → Digest256 := fun i => BitVec.ofNat 256 (0xCAFE0000 + i.val)
    let pkPerm : Fin 128 → Digest256 := fun i => wotsChainIter F_perm i.val 0 3 (skPerm i)
    let truePerm : Fin 128 → Digest256 := fun i => wotsChainIter F_perm i.val 0 (digits i).val (skPerm i)
    let honestSubPerm : SubmittedDigest256ShamirShares 128 := fun i =>
      if h : (digits i).val < 3 then
        let k : Fin 3 := ⟨(digits i).val, h⟩
        let (lo, hi) := splitDigest256Tower128 (truePerm i)
        (pts.map (fun x => RoundPoly.evalCoeffs (lo :: (tape i k).1.1) x),
         pts.map (fun x => RoundPoly.evalCoeffs (hi :: (tape i k).2.1) x))
      else ([], [])
    let corruptSubPerm : SubmittedDigest256ShamirShares 128 := fun i =>
      if i.val = 0 then
        let (lo, hi) := splitDigest256Tower128 (truePerm i)
        ([towerAdd 7 (RoundPoly.evalCoeffs (lo :: [towerX 7]) (towerOne 7)) (towerX 7),
          RoundPoly.evalCoeffs (lo :: [towerX 7]) (towerX 7)],
         pts.map (fun x => RoundPoly.evalCoeffs (hi :: [towerOne 7]) x))
      else
        honestSubPerm i
    (∀ sub : TowerElem 6, towerX 7 ≠ embedTower 6 sub) ∧
    validWotsCsCodeword 128 4 192 digitsNat ∧
    preSteppedDigest256ReconstructAndSelfVerify F_shake pkShake lambdas digits honestSubShake =
      some trueShake ∧
    ((preSteppedDigest256ReconstructAndSelfVerify F_shake pkShake lambdas digits corruptSubShake).isNone = true ∨
      Nonempty (WotsChainCollisionWitness F_shake 4)) ∧
    preSteppedDigest256ReconstructAndSelfVerify F_perm pkPerm lambdas digits honestSubPerm =
      some truePerm ∧
    (preSteppedDigest256ReconstructAndSelfVerify F_perm pkPerm lambdas digits corruptSubPerm).isNone = true := by
  intro pts lambdas digits digitsNat tape masterSeed pkSeed F_shake skShake pkShake trueShake
    honestSubShake corruptSubShake F_perm skPerm pkPerm truePerm honestSubPerm corruptSubPerm
  have hPtsNe : towerOne 7 ≠ towerX 7 := towerOne_ne_towerX 6
  have hX7Nz : towerX 7 ≠ towerZero 7 := by
    intro hZ; exact towerOne_ne_zero 6 (congrArg Prod.snd hZ)
  have hLag : ∀ (c₀ : TowerElem 7) (tail : ShamirPadPoly (TowerElem 7) 1),
      ringDot lambdas (pts.map (fun x => RoundPoly.evalCoeffs (c₀ :: tail.1) x)) = c₀ :=
    fun c₀ tail => lagrange2WeightsTower_eval 7 hPtsNe c₀ tail
  have hLam0Nz : towerMul 7 (towerX 7) (towerInv 7 (towerAdd 7 (towerOne 7) (towerX 7))) ≠ towerZero 7 :=
    lagrange2HeadWeight_ne_zero 7 hPtsNe hX7Nz
  obtain ⟨hHonShake, hSndShake⟩ :=
    preStepped_tower128_digest256_self_verification F_shake skShake tape lambdas pts hLag digits
  obtain ⟨hHonPerm, _⟩ :=
    preStepped_tower128_digest256_self_verification F_perm skPerm tape lambdas pts hLag digits
  have hDigitsNatEq : digitsNat = List.replicate 64 2 ++ List.replicate 64 1 := by
    have hFn : (fun i : Fin 128 => (digits i).val) = (fun i : Fin 128 => if i.val < 64 then 2 else 1) := by
      funext i
      dsimp only [digits]
      by_cases h : i.val < 64 <;> simp [h]
    dsimp only [digitsNat]
    rw [hFn, map_finRange_threshold 128 64 2 1 (by omega)]
  have hCodeword : validWotsCsCodeword 128 4 192 digitsNat := by
    rw [hDigitsNatEq]
    exact tooth_impossible_wots128_target_sum_385_vs_valid_192.2.2
  have hShiftNe : ∀ (node : Digest256),
      joinTower128Digest256
        (ringDot lambdas
          [towerAdd 7 (RoundPoly.evalCoeffs ((splitDigest256Tower128 node).1 :: [towerX 7]) (towerOne 7)) (towerX 7),
           RoundPoly.evalCoeffs ((splitDigest256Tower128 node).1 :: [towerX 7]) (towerX 7)],
         ringDot lambdas
          (pts.map (fun x => RoundPoly.evalCoeffs ((splitDigest256Tower128 node).2 :: [towerOne 7]) x))) ≠ node := by
    intro node hJoinEq
    have hLoHon :
        ringDot lambdas
          [RoundPoly.evalCoeffs ((splitDigest256Tower128 node).1 :: [towerX 7]) (towerOne 7),
           RoundPoly.evalCoeffs ((splitDigest256Tower128 node).1 :: [towerX 7]) (towerX 7)] =
        (splitDigest256Tower128 node).1 :=
      hLag (splitDigest256Tower128 node).1 ⟨[towerX 7], rfl⟩
    have hLoShiftNe :
        ringDot lambdas
          [towerAdd 7 (RoundPoly.evalCoeffs ((splitDigest256Tower128 node).1 :: [towerX 7]) (towerOne 7)) (towerX 7),
           RoundPoly.evalCoeffs ((splitDigest256Tower128 node).1 :: [towerX 7]) (towerX 7)] ≠
        ringDot lambdas
          [RoundPoly.evalCoeffs ((splitDigest256Tower128 node).1 :: [towerX 7]) (towerOne 7),
           RoundPoly.evalCoeffs ((splitDigest256Tower128 node).1 :: [towerX 7]) (towerX 7)] :=
      tooth_unverified_lagrange_accepts_corrupted_share
        (towerMul 7 (towerX 7) (towerInv 7 (towerAdd 7 (towerOne 7) (towerX 7))))
        (RoundPoly.evalCoeffs ((splitDigest256Tower128 node).1 :: [towerX 7]) (towerOne 7))
        (towerX 7)
        [towerMul 7 (towerOne 7) (towerInv 7 (towerAdd 7 (towerOne 7) (towerX 7)))]
        [RoundPoly.evalCoeffs ((splitDigest256Tower128 node).1 :: [towerX 7]) (towerX 7)]
        hLam0Nz hX7Nz
    have hSplitEq := congrArg splitDigest256Tower128 hJoinEq
    rw [split_joinTower128Digest256] at hSplitEq
    exact hLoShiftNe ((congrArg Prod.fst hSplitEq).trans hLoHon.symm)
  let i0 : Fin 128 := ⟨0, by decide⟩
  have hCandOfSome : ∀ (F : Nat → Nat → Digest256 → Digest256) (pk : Fin 128 → Digest256)
      (sub : SubmittedDigest256ShamirShares 128) (cand : Fin 128 → Digest256),
      preSteppedDigest256ReconstructAndSelfVerify F pk lambdas digits sub = some cand →
      cand i0 = joinTower128Digest256 (ringDot lambdas (sub i0).1, ringDot lambdas (sub i0).2) := by
    intro F pk sub cand hSome
    exact preSteppedDigest256_accepted_component F pk lambdas digits sub cand i0 (by decide) hSome
  refine ⟨towerX7_not_in_gf2_64, hCodeword, hHonShake, ?_, hHonPerm, ?_⟩
  · cases hRes : preSteppedDigest256ReconstructAndSelfVerify F_shake pkShake lambdas digits corruptSubShake with
    | none => exact .inl rfl
    | some cand =>
      rcases hSndShake corruptSubShake cand hRes with rfl | hColl
      · exfalso
        have hC0 := hCandOfSome F_shake pkShake corruptSubShake trueShake hRes
        dsimp only [corruptSubShake, i0] at hC0
        exact hShiftNe (trueShake i0) hC0.symm
      · exact .inr hColl
  · cases hRes : preSteppedDigest256ReconstructAndSelfVerify F_perm pkPerm lambdas digits corruptSubPerm with
    | none => rfl
    | some cand =>
      exfalso
      cases extractPreSteppedDigest256Outcome F_perm skPerm lambdas digits corruptSubPerm cand hRes with
      | inl hEq =>
        subst hEq
        have hC0 := hCandOfSome F_perm pkPerm corruptSubPerm truePerm hRes
        dsimp only [corruptSubPerm, i0] at hC0
        exact hShiftNe (truePerm i0) hC0.symm
      | inr w =>
        have hStepEq := w.step_eq
        dsimp only [F_perm] at hStepEq
        let mask := BitVec.ofNat 256 (0x9E3779B97F4A7C15 + w.chainIdx * 257 + w.stepPos)
        have hXor := congrArg (fun z => z ^^^ mask) hStepEq
        rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero,
            BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero] at hXor
        exact w.nodes_ne hXor


/-! ## Exact wire operations and permit-consuming signature execution

The earlier `BeltNetworkTurn` and `QuorumJortsTurn` APIs are generalized algebraic
certificate models, retained for downstream proof compatibility. In particular their
threshold certificate is not Rust's exact peer-roster API. The operational API below
checks Rust records and emits signatures, rather than interpreting those legacy
certificate records as signatures. `qsBGlobalSign` is a scheduled-leaf algebraic evaluator;
allocation is performed by `QsBGlobalAllocator.reserve`, not by that evaluator.
-/

/-- Rust pair-key cSHAKE input: u64 length framing, no domain bytes in the input. -/
def beltPairKeyPreimage (context : List UInt8) (a b : Nat)
    (secrets : List (List UInt8)) : List UInt8 :=
  quorumFrameFields (context :: encodeNatBeBytes 8 (min a b) ::
    encodeNatBeBytes 8 (max a b) :: secrets)

def deriveBeltEchoMacKeyCshake256 (context : List UInt8) (a b : Nat)
    (secrets : List (List UInt8)) : Digest256 :=
  cshake256Digest256 beltEchoKeyTag.data.toList (beltPairKeyPreimage context a b secrets)

/-- Fixed-width Rust echo input, including the commitment to the digits. -/
def beltEchoPreimage (key : Digest256) (sender receiver : Nat)
    (rec : BeltLatchRecord) (binding : Digest256) : List UInt8 :=
  encodeDigest256 key ++ encodeNatBeBytes 8 sender ++ encodeNatBeBytes 8 receiver ++
  encodeNatBeBytes 8 rec.epoch.toNat ++ encodeDigest256 rec.msgDigest ++
  encodeDigest256 rec.retrySalt ++ encodeDigest256 binding

/-- Domain-specific operations: the cSHAKE customization is separate from its input. -/
structure BeltWireCrypto where
  cshake : List UInt8 → List UInt8 → Digest256

def BeltWireCrypto.recordBinding (ops : BeltWireCrypto) (rec : BeltLatchRecord) : Digest256 :=
  ops.cshake beltLatchBindingTag.data.toList (encodeBeltLatchRecord rec)

def BeltWireCrypto.echoTag (ops : BeltWireCrypto) (key : Digest256)
    (sender receiver : Nat) (rec : BeltLatchRecord) : Digest256 :=
  ops.cshake beltEchoMacTag.data.toList
    (beltEchoPreimage key sender receiver rec (ops.recordBinding rec))

def rustBeltWireCrypto : BeltWireCrypto := ⟨cshake256Digest256⟩

theorem rustBeltWireCrypto_binding (rec : BeltLatchRecord) :
    rustBeltWireCrypto.recordBinding rec = beltRecordBindingCshake256 rec := by
  unfold rustBeltWireCrypto BeltWireCrypto.recordBinding beltRecordBindingCshake256
  rfl

theorem rustBeltWireCrypto_echo (key : Digest256) (s r : Nat) (rec : BeltLatchRecord) :
    rustBeltWireCrypto.echoTag key s r rec =
      cshake256Digest256 beltEchoMacTag.data.toList
        (beltEchoPreimage key s r rec (beltRecordBindingCshake256 rec)) := by
  unfold rustBeltWireCrypto BeltWireCrypto.echoTag BeltWireCrypto.recordBinding beltRecordBindingCshake256
  rfl

/-- Echo emission from a healthy persisted latch, parameterized by domain-specific operations. -/
def emitBeltWireEcho {n : Nat} (ops : BeltWireCrypto) (key : Digest256)
    (sender receiver : Fin n) (st : BeltLatchNodeState) : Option (AuthenticatedBeltEcho n) := do
  if st.walPoisoned then none else
    let r ← st.inFlight
    pure
      { sender := sender
        receiver := receiver
        record := r
        binding := ops.recordBinding r
        macTag := ops.echoTag key sender.val receiver.val r }

def verifyBeltWireEcho {n : Nat} (ops : BeltWireCrypto) (key : Digest256)
    (sender receiver : Fin n) (rec : BeltLatchRecord) (echo : AuthenticatedBeltEcho n) : Bool :=
  decide (echo.sender = sender ∧ echo.receiver = receiver ∧ echo.record = rec ∧
    echo.binding = ops.recordBinding rec ∧ echo.macTag = ops.echoTag key sender.val receiver.val rec)

/-- Echo-emission refinement for the actual cSHAKE specialization. -/
theorem emitBeltWireEcho_concrete {n : Nat} (key : Digest256)
    (sender receiver : Fin n) (st : BeltLatchNodeState) (rec : BeltLatchRecord)
    (healthy : st.walPoisoned = false) (bound : st.inFlight = some rec) :
    emitBeltWireEcho rustBeltWireCrypto key sender receiver st =
      some
        { sender := sender
          receiver := receiver
          record := rec
          binding := beltRecordBindingCshake256 rec
          macTag := cshake256Digest256 beltEchoMacTag.data.toList
            (beltEchoPreimage key sender.val receiver.val rec (beltRecordBindingCshake256 rec)) } := by
  simp only [emitBeltWireEcho, healthy, Bool.false_eq_true, ↓reduceIte, bound]
  rfl

/-- Counter occupies the first four bytes of Rust's 32-byte salt; the rest are zero. -/
def quorumCounterSalt (counter : UInt32) : Digest256 :=
  BitVec.ofNat 256 (counter.toNat * 2 ^ 224)

/-- Checked conversion rejects truncated counters, noncanonical salt, and wrapped leaves. -/
def quorumLeafRecordFromLatch (subtreeHeight cIdx : Nat)
    (rec : BeltLatchRecord) : Option QuorumLeafRecord :=
  let leaf := committeeGlobalLeaf (2 ^ subtreeHeight) cIdx rec.epoch.toNat
  let counter := UInt32.ofNat (rec.retrySalt.toNat / 2 ^ 224)
  if rec.epoch.toNat < 2 ^ subtreeHeight ∧ leaf < 2 ^ 64 ∧
      rec.retrySalt = quorumCounterSalt counter then
    some
      { leaf := UInt64.ofNat leaf
        msgHash := rec.msgDigest
        counter := counter
        digits := rec.targetSumDigits }
  else none

/-- `hash.rs::mac32`: domain frame, then key frame, then message frames. -/
def quorumWireMac (H : List UInt8 → Digest256) (key : Digest256)
    (domain : ByteArray) (parts : List (List UInt8)) : Digest256 :=
  H (quorumEncodeFramed domain (encodeDigest256 key :: parts))

def quorumWireEchoMac (H : List UInt8 → Digest256) (key : Digest256)
    (sender receiver cIdx : Nat) (epoch : UInt64) (binding : Digest256) : Digest256 :=
  quorumWireMac H key quorumEchoMacTag
    [encodeNatBeBytes 8 sender, encodeNatBeBytes 8 receiver, encodeNatBeBytes 8 cIdx,
      encodeNatBeBytes 8 epoch.toNat, encodeDigest256 binding]

/-- Exact leaf commitment, not the local latch commitment. -/
def emitQuorumWireEcho {n : Nat} (H : List UInt8 → Digest256)
    (key : Digest256) (subtreeHeight cIdx : Nat) (sender receiver : Fin n)
    (st : BeltLatchNodeState) : Option (QuorumCommitteeEcho n) := do
  if st.walPoisoned then none else
    let r ← st.inFlight
    let leafRec ← quorumLeafRecordFromLatch subtreeHeight cIdx r
    let binding := quorumLeafRecordBinding H leafRec
    pure
      { fromParty := sender
        toParty := receiver
        committeeIdx := cIdx
        epoch := r.epoch
        binding := binding
        mac := quorumWireEchoMac H key sender.val receiver.val cIdx r.epoch binding }

/-- Rust counts every echo from the required peer before authenticating it, so a valid
    echo plus an invalid duplicate still rejects. Extraneous non-peer entries are ignored,
    exactly as Rust's per-peer filter does. Self authorization is the local latch check. -/
def verifyQuorumWirePeers {n : Nat} (H : List UInt8 → Digest256)
    (keys : Fin n → Fin n → Digest256) (Q : CustodiansMask n) (verifier : Fin n)
    (cIdx : Nat) (epoch : UInt64) (rec : QuorumLeafRecord)
    (echoes : List (QuorumCommitteeEcho n)) : Bool :=
  (List.finRange n).all fun peer =>
    if Q.mem peer && decide (peer ≠ verifier) then
      match echoes.filter (fun e => decide (e.fromParty = peer)) with
      | [e] => decide (e.toParty = verifier ∧ e.committeeIdx = cIdx ∧ e.epoch = epoch ∧
          e.binding = quorumLeafRecordBinding H rec ∧
          e.mac = quorumWireEchoMac H (keys peer verifier) peer.val verifier.val
            cIdx epoch (quorumLeafRecordBinding H rec))
      | _ => false
    else true

/-- An accepted required peer supplied the exact record MAC. If that authenticated echo
    was not emitted in the honest transcript, it is a concrete fresh-tag witness. No
    honest-log provenance hypothesis is silently inferred from a Boolean MAC check. -/
theorem verifyQuorumWirePeers_provenance_or_forgery {n : Nat} (H : List UInt8 → Digest256)
    (keys : Fin n → Fin n → Digest256) (Q : CustodiansMask n) (verifier peer : Fin n)
    (cIdx : Nat) (epoch : UInt64) (rec : QuorumLeafRecord)
    (echoes emitted : List (QuorumCommitteeEcho n))
    (required : Q.mem peer = true) (other : peer ≠ verifier)
    (accepted : verifyQuorumWirePeers H keys Q verifier cIdx epoch rec echoes = true) :
    ∃ e ∈ echoes, e.fromParty = peer ∧ e.binding = quorumLeafRecordBinding H rec ∧
      (e ∈ emitted ∨ (e ∉ emitted ∧
        e.mac = quorumWireEchoMac H (keys peer verifier) peer.val verifier.val cIdx epoch
          (quorumLeafRecordBinding H rec))) := by
  unfold verifyQuorumWirePeers at accepted
  have atPeer := List.all_eq_true.mp accepted peer (by simp)
  simp only [required, decide_eq_true other, Bool.and_self, ↓reduceIte] at atPeer
  cases filtered : echoes.filter (fun e => decide (e.fromParty = peer)) with
  | nil => simp only [filtered, Bool.false_eq_true] at atPeer
  | cons e tail =>
    cases tail with
    | cons x xs => simp only [filtered, Bool.false_eq_true] at atPeer
    | nil =>
      simp only [filtered, decide_eq_true_eq] at atPeer
      have inFiltered : e ∈ echoes.filter (fun x => decide (x.fromParty = peer)) := by
        rw [filtered]; exact List.Mem.head _
      obtain ⟨inEchoes, fromPeer⟩ := List.mem_filter.mp inFiltered
      refine ⟨e, inEchoes, of_decide_eq_true fromPeer, atPeer.2.2.2.1, ?_⟩
      if sent : e ∈ emitted then exact .inl sent
      else exact .inr ⟨sent, atPeer.2.2.2.2⟩

/-- The checker obtains its record from the local latch; the requester cannot substitute
    a record, counter or digits after collecting echoes. -/
def checkQuorumWireRelease {n : Nat} (H : List UInt8 → Digest256)
    (keys : Fin n → Fin n → Digest256) (t subtreeHeight : Nat)
    (net : QuorumJortsNetworkState n) (Q : CustodiansMask n) (verifier : Fin n)
    (echoes : List (QuorumCommitteeEcho n)) : Option QuorumLeafRecord := do
  if t = 0 ∨ n ≥ 2 ^ 64 ∨ Q.mem verifier = false then none else
    let cIdx ← committeeIndexOf t Q
    let st := net.slots verifier cIdx
    if st.walPoisoned then none else
      let r ← st.inFlight
      let leafRec ← quorumLeafRecordFromLatch subtreeHeight cIdx r
      if verifyQuorumWirePeers H keys Q verifier cIdx r.epoch leafRec echoes then
        some leafRec
      else none

/-- Proof-carrying permit is tied to this actual network snapshot and exact checker. -/
abbrev QuorumWirePermit {n : Nat} (H : List UInt8 → Digest256)
    (keys : Fin n → Fin n → Digest256) (t h : Nat) (net : QuorumJortsNetworkState n)
    (Q : CustodiansMask n) (v : Fin n) (echoes : List (QuorumCommitteeEcho n)) :=
  { rec : QuorumLeafRecord // checkQuorumWireRelease H keys t h net Q v echoes = some rec }

def issueQuorumWirePermit {n : Nat} (H : List UInt8 → Digest256)
    (keys : Fin n → Fin n → Digest256) (t h : Nat) (net : QuorumJortsNetworkState n)
    (Q : CustodiansMask n) (v : Fin n) (echoes : List (QuorumCommitteeEcho n)) :
    Option (QuorumWirePermit H keys t h net Q v echoes) :=
  match he : checkQuorumWireRelease H keys t h net Q v echoes with
  | none => none
  | some leafRec => some ⟨leafRec, he⟩

/-- Signing inputs are checked against the exact message-bound record carried by the permit. -/
def quorumRecordMatchesMessage (H : List UInt8 → Digest256) (pk : QuorumPublicKey)
    (msg : List UInt8) (rec : QuorumLeafRecord) : Bool :=
  let dig := quorumCounterDigest H rec.msgHash rec.counter
  decide (rec.msgHash = quorumMessageHash H pk rec.leaf msg) &&
  decide (rec.digits = (quorumDigitsFromDigest dig).map (fun d => UInt8.ofNat d.val)) &&
  decide (((quorumDigitsFromDigest dig).map Fin.val).foldr (· + ·) 0 = 192)

/-- A durable reservation is retained even if opening or verification subsequently fails.
    This is an atomic durable-store model; crash/recovery preserves these fields. -/
structure QuorumSigningLedger where
  reserved : List UInt64 := []
  signatures : List QuorumJortsSig := []
  deriving DecidableEq

/-- Public openings contain independently shared, already stepped one-time nodes. No
    polynomial evaluation of the reusable master seed is part of this output type. -/
structure QuorumSteppedOpening where
  leaf : UInt64
  counter : UInt32
  nodes : List Digest256
  deriving DecidableEq

/-- Operational signer consumes a permit through its durable ledger. All signing fields
    come from the checked record, including the chain schedule; failures burn the leaf.
    `masterSeed` and `pk` are fixed for the lifetime of this key's ledger. -/
def signQuorumWirePermit {n : Nat} (H : List UInt8 → Digest256)
    (keys : Fin n → Fin n → Digest256) (t h : Nat) (net : QuorumJortsNetworkState n)
    (Q : CustodiansMask n) (v : Fin n) (echoes : List (QuorumCommitteeEcho n))
    (permit : QuorumWirePermit H keys t h net Q v echoes)
    (masterSeed : Digest256) (pk : QuorumPublicKey) (msg : List UInt8)
    (authPath : List Digest256) (st : QuorumSigningLedger) :
    QuorumSigningLedger × Option QuorumSteppedOpening :=
  let leafRec := permit.val
  if leafRec.leaf ∈ st.reserved then (st, none) else
    let burned := { st with reserved := leafRec.leaf :: st.reserved }
    if quorumRecordMatchesMessage H pk msg leafRec && decide (pk.pkSeed = quorumStagePkSeed H masterSeed) then
      let digits := quorumDigitsFromDigest (quorumCounterDigest H leafRec.msgHash leafRec.counter)
      let sig := quorumJortsReferenceSign H masterSeed leafRec.leaf leafRec.counter digits authPath
      ({ burned with signatures := sig :: st.signatures },
        some { leaf := sig.leaf, counter := sig.counter, nodes := sig.nodes })
    else (burned, none)

theorem signQuorumWirePermit_replay_rejected {n : Nat} (H : List UInt8 → Digest256)
    (keys : Fin n → Fin n → Digest256) (t h : Nat) (net : QuorumJortsNetworkState n)
    (Q : CustodiansMask n) (v : Fin n) (echoes : List (QuorumCommitteeEcho n))
    (permit : QuorumWirePermit H keys t h net Q v echoes)
    (seed : Digest256) (pk : QuorumPublicKey) (msg : List UInt8) (path : List Digest256)
    (st : QuorumSigningLedger) (used : permit.val.leaf ∈ st.reserved) :
    signQuorumWirePermit H keys t h net Q v echoes permit seed pk msg path st = (st, none) := by
  unfold signQuorumWirePermit
  simp only [used, ↓reduceIte]

/-- Every attempted use is durably consumed, including a later failed message check. -/
theorem signQuorumWirePermit_burns {n : Nat} (H : List UInt8 → Digest256)
    (keys : Fin n → Fin n → Digest256) (t h : Nat) (net : QuorumJortsNetworkState n)
    (Q : CustodiansMask n) (v : Fin n) (echoes : List (QuorumCommitteeEcho n))
    (permit : QuorumWirePermit H keys t h net Q v echoes)
    (seed : Digest256) (pk : QuorumPublicKey) (msg : List UInt8) (path : List Digest256)
    (st : QuorumSigningLedger) :
    permit.val.leaf ∈
      (signQuorumWirePermit H keys t h net Q v echoes permit seed pk msg path st).1.reserved := by
  unfold signQuorumWirePermit
  dsimp only
  split
  next used => exact used
  next fresh =>
    split <;> exact List.Mem.head _

/-- A produced opening is exactly the stepped chain vector for the authenticated record. -/
theorem signQuorumWirePermit_output {n : Nat} (H : List UInt8 → Digest256)
    (keys : Fin n → Fin n → Digest256) (t h : Nat) (net : QuorumJortsNetworkState n)
    (Q : CustodiansMask n) (v : Fin n) (echoes : List (QuorumCommitteeEcho n))
    (permit : QuorumWirePermit H keys t h net Q v echoes)
    (seed : Digest256) (pk : QuorumPublicKey) (msg : List UInt8) (path : List Digest256)
    (st : QuorumSigningLedger) (out : QuorumSteppedOpening)
    (produced : (signQuorumWirePermit H keys t h net Q v echoes
      permit seed pk msg path st).2 = some out) :
    checkQuorumWireRelease H keys t h net Q v echoes = some permit.val ∧
    out.leaf = permit.val.leaf ∧ out.counter = permit.val.counter ∧
    out.nodes = (quorumJortsReferenceSign H seed permit.val.leaf permit.val.counter
      (quorumDigitsFromDigest (quorumCounterDigest H permit.val.msgHash permit.val.counter)) path).nodes := by
  refine ⟨permit.property, ?_⟩
  unfold signQuorumWirePermit at produced
  dsimp only at produced
  split at produced
  next used => cases produced
  next fresh =>
    split at produced
    next accepted =>
      cases Option.some.inj produced
      exact ⟨rfl, rfl, rfl⟩
    next rejected => cases produced

/-- Reusing the same permit after any attempt produces no second opening. -/
theorem signQuorumWirePermit_one_attempt {n : Nat} (H : List UInt8 → Digest256)
    (keys : Fin n → Fin n → Digest256) (t h : Nat) (net : QuorumJortsNetworkState n)
    (Q : CustodiansMask n) (v : Fin n) (echoes : List (QuorumCommitteeEcho n))
    (permit : QuorumWirePermit H keys t h net Q v echoes)
    (seed : Digest256) (pk : QuorumPublicKey) (msg : List UInt8) (path : List Digest256)
    (st : QuorumSigningLedger) :
    let next := (signQuorumWirePermit H keys t h net Q v echoes permit seed pk msg path st).1
    (signQuorumWirePermit H keys t h net Q v echoes permit seed pk msg path next).2 = none := by
  dsimp only
  rw [signQuorumWirePermit_replay_rejected H keys t h net Q v echoes permit seed pk msg path _
    (signQuorumWirePermit_burns H keys t h net Q v echoes permit seed pk msg path st)]

/-- Safety is about actual signature outputs, not only released authorization records. -/
def QuorumSigningLedger.Safe (st : QuorumSigningLedger) : Prop :=
  (∀ sig ∈ st.signatures, sig.leaf ∈ st.reserved) ∧
  (∀ a ∈ st.signatures, ∀ b ∈ st.signatures, a.leaf = b.leaf → a = b)

private theorem signingLedger_burn_safe (st : QuorumSigningLedger) (leaf : UInt64)
    (safe : st.Safe) : ({ st with reserved := leaf :: st.reserved } : QuorumSigningLedger).Safe := by
  refine ⟨?_, safe.2⟩
  intro sig hs
  exact List.Mem.tail _ (safe.1 sig hs)

private theorem signingLedger_cons_safe (st : QuorumSigningLedger) (sig : QuorumJortsSig)
    (safe : st.Safe) (fresh : sig.leaf ∉ st.reserved) :
    ({ reserved := sig.leaf :: st.reserved, signatures := sig :: st.signatures } :
      QuorumSigningLedger).Safe := by
  constructor
  · intro a ha
    dsimp only at ha
    rcases List.mem_cons.mp ha with rfl | haTail
    · exact List.Mem.head _
    · exact List.Mem.tail _ (safe.1 a haTail)
  · intro a ha b hb heq
    dsimp only at ha hb
    rcases List.mem_cons.mp ha with rfl | haTail
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · rfl
      · have used := safe.1 b hbTail
        rw [← heq] at used
        exact False.elim (fresh used)
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · have used := safe.1 a haTail
        rw [heq] at used
        exact False.elim (fresh used)
      · exact safe.2 a haTail b hbTail heq

theorem signQuorumWirePermit_preserves_safety {n : Nat} (H : List UInt8 → Digest256)
    (keys : Fin n → Fin n → Digest256) (t h : Nat) (net : QuorumJortsNetworkState n)
    (Q : CustodiansMask n) (v : Fin n) (echoes : List (QuorumCommitteeEcho n))
    (permit : QuorumWirePermit H keys t h net Q v echoes)
    (seed : Digest256) (pk : QuorumPublicKey) (msg : List UInt8) (path : List Digest256)
    (st : QuorumSigningLedger) (safe : st.Safe) :
    (signQuorumWirePermit H keys t h net Q v echoes permit seed pk msg path st).1.Safe := by
  unfold signQuorumWirePermit
  dsimp only
  split
  next used => exact safe
  next fresh =>
    split
    next accepted => exact signingLedger_cons_safe st _ safe fresh
    next rejected => exact signingLedger_burn_safe st _ safe

/-- Exact wire execution retains the existing durable latch transition system but routes
    observable echoes and signature openings through the checked wire APIs. -/
structure QuorumWireNetworkState (n : Nat) where
  latches : QuorumJortsNetworkState n
  echoes : List (QuorumCommitteeEcho n) := []
  signing : QuorumSigningLedger := {}

inductive QuorumWireTurn (n : Nat) where
  | latch (turn : QuorumJortsTurn n)
  | echo (sender receiver : Fin n) (committee : CustodiansMask n)
  | sign (verifier : Fin n) (committee : CustodiansMask n)
      (msg : List UInt8) (path : List Digest256) (echoes : List (QuorumCommitteeEcho n))

/-- Key identity, public parameters and corrupt set are fixed across the entire trace. -/
def stepQuorumWireNetwork {n : Nat} (H : List UInt8 → Digest256)
    (keys : Fin n → Fin n → Digest256) (Corrupt : CustodiansMask n)
    (seed : Digest256) (pk : QuorumPublicKey) (t height : Nat)
    (st : QuorumWireNetworkState n) (turn : QuorumWireTurn n) : QuorumWireNetworkState n :=
  match turn with
  | .latch action =>
    { st with
      latches := stepQuorumJorts H (fun k bs => H (encodeDigest256 k ++ bs))
        keys Corrupt t height t st.latches action }
  | .echo sender receiver Q =>
    if Corrupt.mem sender || !Q.mem sender then st else
      match committeeIndexOf t Q with
      | none => st
      | some idx =>
        match emitQuorumWireEcho H (keys sender receiver) height idx sender receiver
            (st.latches.slots sender idx) with
        | none => st
        | some echo => { st with echoes := echo :: st.echoes }
  | .sign verifier Q msg path echoes =>
    if Corrupt.mem verifier then st else
      match issueQuorumWirePermit H keys t height st.latches Q verifier echoes with
      | none => st
      | some permit =>
        { st with
          signing := (signQuorumWirePermit H keys t height st.latches Q verifier
            echoes permit seed pk msg path st.signing).1 }

def runQuorumWireTrace {n : Nat} (H : List UInt8 → Digest256)
    (keys : Fin n → Fin n → Digest256) (Corrupt : CustodiansMask n)
    (seed : Digest256) (pk : QuorumPublicKey) (t height : Nat)
    (st : QuorumWireNetworkState n) : List (QuorumWireTurn n) → QuorumWireNetworkState n
  | [] => st
  | turn :: rest => runQuorumWireTrace H keys Corrupt seed pk t height
      (stepQuorumWireNetwork H keys Corrupt seed pk t height st turn) rest

theorem stepQuorumWireNetwork_preserves_safety {n : Nat} (H : List UInt8 → Digest256)
    (keys : Fin n → Fin n → Digest256) (Corrupt : CustodiansMask n)
    (seed : Digest256) (pk : QuorumPublicKey) (t height : Nat)
    (st : QuorumWireNetworkState n) (turn : QuorumWireTurn n) (safe : st.signing.Safe) :
    (stepQuorumWireNetwork H keys Corrupt seed pk t height st turn).signing.Safe := by
  cases turn with
  | latch action => exact safe
  | echo sender receiver Q =>
    unfold stepQuorumWireNetwork
    dsimp only
    by_cases hDenied : (Corrupt.mem sender || !Q.mem sender) = true
    · simp only [hDenied, ↓reduceIte]; exact safe
    · simp only [Bool.not_eq_true] at hDenied
      simp only [hDenied, Bool.false_eq_true, ↓reduceIte]
      cases committeeIndexOf t Q with
      | none => dsimp only; exact safe
      | some idx =>
        dsimp only
        cases emitQuorumWireEcho H (keys sender receiver) height idx sender receiver
            (st.latches.slots sender idx) <;> dsimp only <;> exact safe
  | sign verifier Q msg path echoes =>
    unfold stepQuorumWireNetwork
    dsimp only
    by_cases hCorrupt : Corrupt.mem verifier = true
    · simp only [hCorrupt, ↓reduceIte]; exact safe
    · simp only [Bool.not_eq_true] at hCorrupt
      simp only [hCorrupt, Bool.false_eq_true, ↓reduceIte]
      cases issueQuorumWirePermit H keys t height st.latches Q verifier echoes with
      | none => dsimp only; exact safe
      | some permit =>
        dsimp only
        exact signQuorumWirePermit_preserves_safety H keys t height st.latches Q verifier
          echoes permit seed pk msg path st.signing safe

/-- End-to-end trace theorem: for every exact wire trace, two actual signature outputs
    at the same leaf are identical. The ledger is shared for this key and survives crashes;
    distributed replication of that ledger is a separate implementation obligation. -/
theorem runQuorumWireTrace_signature_safety {n : Nat} (H : List UInt8 → Digest256)
    (keys : Fin n → Fin n → Digest256) (Corrupt : CustodiansMask n)
    (seed : Digest256) (pk : QuorumPublicKey) (t height : Nat)
    (st : QuorumWireNetworkState n) (trace : List (QuorumWireTurn n))
    (safe : st.signing.Safe) :
    (runQuorumWireTrace H keys Corrupt seed pk t height st trace).signing.Safe := by
  induction trace generalizing st with
  | nil => exact safe
  | cons turn rest ih =>
    exact ih _ (stepQuorumWireNetwork_preserves_safety H keys Corrupt seed pk t height st turn safe)

theorem emptyQuorumSigningLedger_safe : ({} : QuorumSigningLedger).Safe := by
  constructor <;> intro _ h <;> cases h

/-- Single durable allocator shared by all QS-B responding committees. Natural-number
    cursor arithmetic cannot wrap; conversion occurs only after the range check. -/
structure QsBGlobalAllocator where
  nextLeaf : Nat := 0
  deriving DecidableEq

def QsBGlobalAllocator.reserve (height : Nat) (st : QsBGlobalAllocator) :
    Option (UInt64 × QsBGlobalAllocator) :=
  if st.nextLeaf < 2 ^ height ∧ st.nextLeaf < 2 ^ 64 then
    some (UInt64.ofNat st.nextLeaf, ⟨st.nextLeaf + 1⟩)
  else none

theorem QsBGlobalAllocator.reserve_bounds {height : Nat} {st next : QsBGlobalAllocator}
    {leaf : UInt64} (h : st.reserve height = some (leaf, next)) :
    leaf.toNat = st.nextLeaf ∧ st.nextLeaf < 2 ^ height ∧
      st.nextLeaf < 2 ^ 64 ∧ next.nextLeaf = st.nextLeaf + 1 := by
  unfold QsBGlobalAllocator.reserve at h
  split at h
  next good =>
    rcases Prod.mk.inj (Option.some.inj h) with ⟨rfl, rfl⟩
    exact ⟨uint64_toNat_ofNat_of_lt good.2, good.1, good.2, rfl⟩
  next bad => cases h

/-- Consecutive reservations cannot collide even when different committees respond. -/
theorem QsBGlobalAllocator.reserve_disjoint {height : Nat}
    {s₀ s₁ s₂ : QsBGlobalAllocator} {l₁ l₂ : UInt64}
    (h₁ : s₀.reserve height = some (l₁, s₁))
    (h₂ : s₁.reserve height = some (l₂, s₂)) : l₁ ≠ l₂ := by
  obtain ⟨he₁, _, _, hn₁⟩ := QsBGlobalAllocator.reserve_bounds h₁
  obtain ⟨he₂, _, _, _⟩ := QsBGlobalAllocator.reserve_bounds h₂
  intro same
  have := congrArg UInt64.toNat same
  omega

/-- Permit-consuming global signing. The one shared cursor is reserved before invoking
    the checked signer and is retained even when the signer rejects. A partition cannot
    select a different global leaf by passing an independent signing argument. -/
def signQsBWirePermit {n : Nat} (H : List UInt8 → Digest256)
    (keys : Fin n → Fin n → Digest256) (t h : Nat) (net : QuorumJortsNetworkState n)
    (Q : CustodiansMask n) (v : Fin n) (echoes : List (QuorumCommitteeEcho n))
    (permit : QuorumWirePermit H keys t h net Q v echoes)
    (seed : Digest256) (pk : QuorumPublicKey) (msg : List UInt8) (path : List Digest256)
    (allocator : QsBGlobalAllocator) (ledger : QuorumSigningLedger) :
    QsBGlobalAllocator × QuorumSigningLedger × Option QuorumSteppedOpening :=
  if permit.val.leaf.toNat = allocator.nextLeaf then
    match allocator.reserve pk.height.toNat with
    | none => (allocator, ledger, none)
    | some (_, next) =>
      let result := signQuorumWirePermit H keys t h net Q v echoes permit seed pk msg path ledger
      (next, result.1, result.2)
  else (allocator, ledger, none)

/-- The global allocator cannot bypass the authenticated-record signer. -/
theorem signQsBWirePermit_output_authorized {n : Nat} (H : List UInt8 → Digest256)
    (keys : Fin n → Fin n → Digest256) (t h : Nat) (net : QuorumJortsNetworkState n)
    (Q : CustodiansMask n) (v : Fin n) (echoes : List (QuorumCommitteeEcho n))
    (permit : QuorumWirePermit H keys t h net Q v echoes)
    (seed : Digest256) (pk : QuorumPublicKey) (msg : List UInt8) (path : List Digest256)
    (allocator : QsBGlobalAllocator) (ledger : QuorumSigningLedger) (out : QuorumSteppedOpening)
    (produced : (signQsBWirePermit H keys t h net Q v echoes permit seed pk msg path
      allocator ledger).2.2 = some out) :
    out.leaf.toNat = allocator.nextLeaf ∧
      checkQuorumWireRelease H keys t h net Q v echoes = some permit.val := by
  unfold signQsBWirePermit at produced
  split at produced
  next current =>
    cases allocated : allocator.reserve pk.height.toNat with
    | none => simp only [allocated] at produced; cases produced
    | some allocation =>
      rcases allocation with ⟨leaf, next⟩
      simp only [allocated] at produced
      obtain ⟨authorized, leafEq, _⟩ := signQuorumWirePermit_output H keys t h net Q v echoes
        permit seed pk msg path ledger out produced
      exact ⟨(congrArg UInt64.toNat leafEq).trans current, authorized⟩
  next mismatch => cases produced

/-- Allocated algebraic QS-B evaluator used for the quorum-independence theorem below.
    The permit-consuming operational entry is `signQsBWirePermit`. The responding subset changes interpolation inputs only;
    it cannot select a leaf or a partition. -/
def qsBAllocateAndSign {d : Nat} (H : List UInt8 → Digest256) (seed : Digest256)
    (height : Nat) (st : QsBGlobalAllocator) (counter : UInt32) (digits : List (Fin 4))
    (path : List Digest256)
    (tape : Fin digits.length → ShamirPadPoly (TowerElem 7) d × ShamirPadPoly (TowerElem 7) d)
    (pts lambdas : List (TowerElem 7)) : QsBGlobalAllocator × Option QuorumJortsSig :=
  match st.reserve height with
  | none => (st, none)
  | some (leaf, next) =>
    (next, some (qsBGlobalSign H seed leaf counter digits path tape pts lambdas))

/-- Actual QS-B signatures expose the allocated, representable global leaf. -/
theorem qsBAllocateAndSign_allocated {d : Nat} (H : List UInt8 → Digest256) (seed : Digest256)
    (height : Nat) (st next : QsBGlobalAllocator) (counter : UInt32) (digits : List (Fin 4))
    (path : List Digest256)
    (tape : Fin digits.length → ShamirPadPoly (TowerElem 7) d × ShamirPadPoly (TowerElem 7) d)
    (pts lambdas : List (TowerElem 7)) (sig : QuorumJortsSig)
    (h : qsBAllocateAndSign H seed height st counter digits path tape pts lambdas = (next, some sig)) :
    sig.leaf.toNat = st.nextLeaf ∧ next.nextLeaf = st.nextLeaf + 1 ∧ st.nextLeaf < 2 ^ 64 := by
  cases allocated : st.reserve height with
  | none =>
    simp only [qsBAllocateAndSign, allocated] at h
    have impossible := congrArg Prod.snd h
    cases impossible
  | some result =>
    rcases result with ⟨leaf, after⟩
    simp only [qsBAllocateAndSign, allocated] at h
    rcases Prod.mk.inj h with ⟨rfl, hS⟩
    cases Option.some.inj hS
    obtain ⟨hl, _, hFit, hn⟩ := QsBGlobalAllocator.reserve_bounds allocated
    exact ⟨hl, hn, hFit⟩

/-- Quorum switching cannot make consecutive signature outputs overlap. This statement
    quantifies over distinct Shamir quorums and all their private polynomial tapes. -/
theorem qsB_signature_quorum_switching_disjoint {d₁ d₂ : Nat}
    (H : List UInt8 → Digest256) (seed : Digest256) (height : Nat)
    (s₀ s₁ s₂ : QsBGlobalAllocator) (c₁ c₂ : UInt32) (ds₁ ds₂ : List (Fin 4))
    (path₁ path₂ : List Digest256)
    (tape₁ : Fin ds₁.length → ShamirPadPoly (TowerElem 7) d₁ × ShamirPadPoly (TowerElem 7) d₁)
    (tape₂ : Fin ds₂.length → ShamirPadPoly (TowerElem 7) d₂ × ShamirPadPoly (TowerElem 7) d₂)
    (pts₁ ws₁ pts₂ ws₂ : List (TowerElem 7)) (sig₁ sig₂ : QuorumJortsSig)
    (h₁ : qsBAllocateAndSign H seed height s₀ c₁ ds₁ path₁ tape₁ pts₁ ws₁ = (s₁, some sig₁))
    (h₂ : qsBAllocateAndSign H seed height s₁ c₂ ds₂ path₂ tape₂ pts₂ ws₂ = (s₂, some sig₂)) :
    sig₁.leaf ≠ sig₂.leaf := by
  obtain ⟨hl₁, hn₁, _⟩ := qsBAllocateAndSign_allocated H seed height s₀ s₁ c₁ ds₁ path₁ tape₁ pts₁ ws₁ sig₁ h₁
  obtain ⟨hl₂, _, _⟩ := qsBAllocateAndSign_allocated H seed height s₁ s₂ c₂ ds₂ path₂ tape₂ pts₂ ws₂ sig₂ h₂
  intro same
  have := congrArg UInt64.toNat same
  omega

/-- Exported QS-A success carries the bounds checked by execution, not caller hypotheses. -/
theorem qsAPartitionedSign_success_bounds {n : Nat}
    (H : List UInt8 → Digest256) (seed : Digest256) (t height : Nat)
    (Q : CustodiansMask n) (epoch : Nat) (counter : UInt32) (digits : List (Fin 4))
    (path : List Digest256) (tape : QsAChainShareTape t digits.length) (sig : QuorumJortsSig)
    (h : qsAPartitionedSign H seed t height Q epoch counter digits path tape = some sig) :
    0 < t ∧ epoch < 2 ^ height ∧
      ∃ idx, committeeIndexOf t Q = some idx ∧
        committeeGlobalLeaf (2 ^ height) idx epoch < 2 ^ 64 ∧
        sig.leaf.toNat = committeeGlobalLeaf (2 ^ height) idx epoch := by
  unfold qsAPartitionedSign at h
  split at h
  next => cases h
  next idx hi =>
    split at h
    next good =>
      cases Option.some.inj h
      exact ⟨good.1, good.2.1, idx, hi, good.2.2,
        uint64_toNat_ofNat_of_lt good.2.2⟩
    next bad => cases h


/-- Empty enrollment reaches the ledger invariant before the first signing attempt. -/
theorem inhabited_signing_ledger : ∃ st : QuorumSigningLedger, st.Safe :=
  ⟨{}, emptyQuorumSigningLedger_safe⟩

theorem tooth_used_quorum_permit_cannot_release {n : Nat} (H : List UInt8 → Digest256)
    (keys : Fin n → Fin n → Digest256) (t h : Nat) (net : QuorumJortsNetworkState n)
    (Q : CustodiansMask n) (v : Fin n) (echoes : List (QuorumCommitteeEcho n))
    (permit : QuorumWirePermit H keys t h net Q v echoes)
    (seed : Digest256) (pk : QuorumPublicKey) (msg : List UInt8) (path : List Digest256)
    (st : QuorumSigningLedger) (used : permit.val.leaf ∈ st.reserved)
    (out : QuorumSteppedOpening) :
    (signQuorumWirePermit H keys t h net Q v echoes permit seed pk msg path st).2 ≠ some out := by
  rw [signQuorumWirePermit_replay_rejected H keys t h net Q v echoes permit seed pk msg path st used]
  intro bad
  cases bad

#verify_inhabited signingLedger_burn_safe inhabited_signing_ledger
#tooth_pair runQuorumWireTrace_signature_safety vs tooth_used_quorum_permit_cannot_release

end Qsag
end
