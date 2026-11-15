module
/-
# Qsag.Custody.JortsBeltLatchAndQuorumSwitching — `Jorts` (Modes 3A & 3B), `BeltLatch`, `(t, n, f)` BFT Quorum-Switching, Committee-Partitioned Subtrees & Self-Verifying Pre-Stepped `GF(2^128)` Shamir `WOTS+C`

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
     `"QSAG.BELT.LATCH.WAL.MAC/v2"`) and all 12 `quorum_jorts.rs` domain tags
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

public import Qsag.Math.Digest256
public import Qsag.Math.Constructive
public import Qsag.Exec.SimulationSpine
public import Qsag.Math.Goldilocks
public import Qsag.Math.BinaryTower
public import Qsag.Oracle.UcGames
public import Qsag.Protocol.Threshold.BaggyAndRss256Security
public import Qsag.Custody.CustodySuiteFull
import all Qsag.Oracle.UcGames
import all Qsag.Protocol.Threshold.BaggyAndRss256Security

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

/-- Exact 26-byte domain tag `"QSAG.BELT.LATCH.WAL.MAC/v2"` (`belt_latch.rs:68`). -/
def beltLatchWalMacTag : ByteArray :=
  ByteArray.mk #[0x51, 0x53, 0x41, 0x47, 0x2E, 0x42, 0x45, 0x4C, 0x54, 0x2E, 0x4C, 0x41, 0x54,
                 0x43, 0x48, 0x2E, 0x57, 0x41, 0x4C, 0x2E, 0x4D, 0x41, 0x43, 0x2F, 0x76, 0x32]

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

/-- Durable WAL seal tag under `"QSAG.BELT.LATCH.WAL.MAC/v2"` (`FsBeltWal::tag`, `belt_latch.rs:271-273`). -/
def computeBeltWalSealTag
    (H : List UInt8 → Digest256) (walKey : Digest256) (lockSeal : List UInt8)
    (generation : UInt64) (body : List UInt8) : Digest256 :=
  H (encodeMultiFrame [beltLatchWalMacTag.data.toList,
    encodeMultiFrame [encodeDigest256 walKey, lockSeal, encodeNatBeBytes 8 generation.toNat, body]])

theorem computeBeltWalSealTag_binding (H : List UInt8 → Digest256)
    {k₁ k₂ : Digest256} {l₁ l₂ b₁ b₂ : List UInt8} {g₁ g₂ : UInt64}
    (hTag : computeBeltWalSealTag H k₁ l₁ g₁ b₁ = computeBeltWalSealTag H k₂ l₂ g₂ b₂) :
    (k₁ = k₂ ∧ l₁ = l₂ ∧ encodeNatBeBytes 8 g₁.toNat = encodeNatBeBytes 8 g₂.toNat ∧ b₁ = b₂) ∨
      Nonempty (HashCollision256 H) := by
  let pre₁ := encodeMultiFrame [beltLatchWalMacTag.data.toList,
    encodeMultiFrame [encodeDigest256 k₁, l₁, encodeNatBeBytes 8 g₁.toNat, b₁]]
  let pre₂ := encodeMultiFrame [beltLatchWalMacTag.data.toList,
    encodeMultiFrame [encodeDigest256 k₂, l₂, encodeNatBeBytes 8 g₂.toNat, b₂]]
  if hPre : pre₁ = pre₂ then
    have hOuter := encodeMultiFrame_injective hPre
    injection hOuter with _ hRest
    injection hRest with hInner _
    obtain ⟨hk, hl, hg, hb⟩ := list4_eq_iff (encodeMultiFrame_injective hInner)
    exact .inl ⟨encodeDigest256_injective hk, hl, hg, hb⟩
  else exact .inr ⟨⟨pre₁, pre₂, hPre, hTag⟩⟩

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
