module

public import Qsag.Custody.JortsBeltLatchAndQuorumSwitching
public import Qsag.Custody.SeparatedCustodyCollision
public import Qsag.Protocol.Signing.ProdHashGameReductions
public import Qsag.Protocol.Threshold.ThresholdMpc
public import Qsag.Exec.SimulationSpine
import all Qsag.Oracle.Keccak
import all Qsag.Custody.JortsBeltLatchAndQuorumSwitching
import all Qsag.Exec.SimulationSpine
import all Qsag.Protocol.Threshold.ThresholdMpc
import all Qsag.Protocol.Threshold.MaliciousSecurity
import all Qsag.Custody.CompleteMediationBoundary
import all Qsag.Custody.SeparatedCustodyCore
import all Qsag.Custody.SeparatedCustodySpine
import all Qsag.Custody.SeparatedCustodyCollision
import Qsag.Tactic.AssuranceKit

/-!
# `(t, n)` Shamir Single-Validator Threshold Custody Refinement

## Architectural Scope (`M3` & `M2` Closure)

`SeparatedCustody{Core,Spine,Policy,History,Collision}` and `CompleteMediationBoundary`
model `n` **independently keyed** custodian vaults (`keys : Nat → PqSecretKey`), where
each custodian produces an individual stateful Jorts signature under its own key and a
coordinator checks `t` distinct custodian certificates. By contrast, `BftShamirJorts`
(`QS-B` in `JortsBeltLatchAndQuorumSwitching`) and dynamic Shamir threshold custody
reconstruct a **single enrolled validator public key** `pk` from any `t`-of-`n` Shamir
shares over `GF(2^128)` (`TowerElem 7`), gated by a `2 * q > n + f` pairwise-MAC
`BeltLatch` certificate.

This module bridges `CompleteMediationBoundary` / `SeparatedCustody` to single-validator
`(t, n)` Shamir + `BeltLatch` custody:

1. **Single-Validator `QuorumPublicKey` Enrolment, Merkle Verification & Constructive Extraction
   (`deriveQuorumValidatorPublicKey`, `verifyQuorumJortsSigAt`, `verifyQuorumJortsSig`,
   `verifyQuorumJortsSigAt_extract_reference_or_collision`)**:
   - Defines exact binary Merkle root derivation (`quorumTreeNode`), authentication path
     generation (`quorumAuthPath`), path verification (`quorumWalkMerklePath`), and full
     single-validator `QuorumJortsSig` verification (`verifyQuorumJortsSig`).
   - Constructively (`PSum`, `0 Classical.choice`) proves that **every** signature
     accepted by `verifyQuorumJortsSigAt` under the enrolled `validatorPk` either carries
     the exact single-validator reference WOTS+C chain nodes
     `(quorumJortsReferenceSign ...).nodes` or yields an explicit `WotsChainCollisionWitness`
     / `HashCollision256 H`.

2. **Per-Custodian `LockstepSim` & `ForwardSim` to `CompleteMediationBoundary`
   (`shamirCustodianLockstepSim`, `shamirCustodianForwardSim`)**:
   - Packages each custodian's `BeltLatch`-gated `Custody.Vault` (enforcing durable
     monotone `nextLeaf`, `nextRound`, `spent ≤ cap`, BDOZ `Custody.checkRound` approval,
     `2 * q > n + f` `BeltLatch` quorum echo certification on `mint`, and one-time handle
     burn on `(t, n)` pre-stepped `GF(2^128)²` Shamir share release) as a
     `SimulationSpine.PartyMachine` that lockstep/forward-simulates the abstract
     complete-mediation vault machine across arbitrary mint, share-release, forget, and
     crash schedules.

3. **Multi-Turn `(t, n)` Shamir + `2q > n + f` `BeltLatch` Epoch Non-Equivocation
   (`shamir_custody_epoch_non_equivocation`)**:
   - Across any multi-turn open-world network trace `runShamirCustodyTrace` with
     `maskCard Corrupt ≤ f`, `f < t`, and `2 * q > n + f`:
     * **(a) Per-Honest-Custodian Leaf Uniqueness:** No honest custodian ever releases
       Shamir shares for two distinct `Custody.Intent`s at the same leaf epoch.
     * **(b) Global `(q, t)` Epoch Non-Equivocation:** No two distinct intents `r₁ ≠ r₂`
       at the same leaf epoch (`r₁.leaf = r₂.leaf`) can both obtain `q`-latch certified
       mints and `t`-custodian Shamir share releases unless an explicit
       `PairwiseEchoMacForgery` or `HashCollision256 H` witness is constructively
       extracted (`PSum` / disjunction, `0 Classical.choice`).

4. **Combined Single-Validator Signature Soundness, Quorum Invariance & Production Hypertree Bridge
   (`shamir_custody_combined_sig_verifies_or_collision`,
   `shamir_custody_single_validator_pq_bridge`)**:
   - Any combined signature reconstructed from `t` honest pre-stepped `GF(2^128)²`
     Shamir share openings equals `quorumJortsReferenceSign` (bit-for-bit invariant
     across any two honest `t`-subsets) and verifies under the single enrolled
     `validatorPk`; any share-corrupted combiner output accepted by self-verification +
     Merkle check constructively equals the reference signature or yields a
     `WotsChainCollisionWitness` (`HashCollision256 H`).
   - Connects single-validator `mpcEvalProductionStatefulSign` (`ThresholdMpc`) to
     `ProdCollisionExtraction` and the seed-withheld `Within` challenger games of
     `ProdHashGameReductions`.
-/

public section

namespace Qsag

set_option autoImplicit false
set_option maxRecDepth 4096

/-! ## §1. Single-Validator `QuorumPublicKey` Merkle Enrolment, Verification & Collision Extraction -/

/-- Canonical domain-framed intent byte payload encoding all 5 fields of `Custody.Intent`
    (`session`, `round`, `leaf`, `spend`, `message`) via `encodeMultiFrame` + `leb128` with an
    explicit byte-literal domain tag (zero `@[extern]` `String.toUTF8` calls for pure kernel
    reducibility). -/
def intentCanonicalPayload (r : Custody.Intent) : List UInt8 :=
  encodeMultiFrame
    [[0x51, 0x53, 0x41, 0x47, 0x2e, 0x53, 0x48, 0x41, 0x4d, 0x49, 0x52],
     leb128 r.session, leb128 r.round, leb128 r.leaf, leb128 r.spend, r.message]

theorem intentCanonicalPayload_injective {r₁ r₂ : Custody.Intent}
    (h : intentCanonicalPayload r₁ = intentCanonicalPayload r₂) : r₁ = r₂ := by
  have hf := encodeMultiFrame_injective h
  simp only [List.cons.injEq] at hf
  have hLeb : ∀ {a b : Nat}, leb128 a = leb128 b → a = b := fun {a b} hEq =>
    (leb128_prefix_inj (show leb128 a ++ [] = leb128 b ++ [] by simpa using hEq)).1
  have hs := hLeb hf.2.1
  have hr := hLeb hf.2.2.1
  have hl := hLeb hf.2.2.2.1
  have hv := hLeb hf.2.2.2.2.1
  have hm := hf.2.2.2.2.2.1
  cases r₁; cases r₂
  simp_all only

/-- Public WOTS+C chain endpoints (`3` steps from `quorumStageChainSk`) across `L` chains for
    scheduled leaf `leaf` under `masterSeed`. -/
def quorumHonestChainEnds (L : Nat) (H : List UInt8 → Digest256)
    (masterSeed : Digest256) (leaf : UInt64) : List Digest256 :=
  let pkSeed := quorumStagePkSeed H masterSeed
  (List.finRange L).map (fun idx =>
    let sk₀ := quorumStageChainSk H masterSeed leaf (UInt32.ofNat idx.1)
    wotsChainIter (quorumChainStep H pkSeed leaf) idx.1 0 3 sk₀)

theorem quorumHonestChainEnds_length (L : Nat) (H : List UInt8 → Digest256)
    (masterSeed : Digest256) (leaf : UInt64) :
    (quorumHonestChainEnds L H masterSeed leaf).length = L := by
  simp [quorumHonestChainEnds]

/-- Honest Merkle leaf digest at `leaf` committing to all `L` WOTS+C chain endpoints. -/
def quorumHonestLeafDigest (L : Nat) (H : List UInt8 → Digest256)
    (masterSeed : Digest256) (leaf : UInt64) : Digest256 :=
  let pkSeed := quorumStagePkSeed H masterSeed
  quorumLeafHash H pkSeed leaf (quorumHonestChainEnds L H masterSeed leaf)

/-- Binary Merkle tree node at `(level, idx)` over leaf family `leafFn : UInt64 → Digest256`. -/
def quorumTreeNode (H : List UInt8 → Digest256) (pkSeed : Digest256)
    (leafFn : UInt64 → Digest256) : Nat → Nat → Digest256
  | 0, idx => leafFn (UInt64.ofNat idx)
  | level + 1, idx =>
    let left := quorumTreeNode H pkSeed leafFn level (2 * idx)
    let right := quorumTreeNode H pkSeed leafFn level (2 * idx + 1)
    quorumMerkleNodeHash H pkSeed (UInt8.ofNat level) (UInt64.ofNat idx) left right

/-- Sibling authentication path of length `rem` starting from `(level, idx)`. -/
def quorumAuthPath (H : List UInt8 → Digest256) (pkSeed : Digest256)
    (leafFn : UInt64 → Digest256) : Nat → Nat → Nat → List Digest256
  | 0, _, _ => []
  | rem + 1, level, idx =>
    let sibIdx := if idx % 2 = 0 then idx + 1 else idx - 1
    quorumTreeNode H pkSeed leafFn level sibIdx ::
      quorumAuthPath H pkSeed leafFn rem (level + 1) (idx / 2)

theorem quorumAuthPath_length (H : List UInt8 → Digest256) (pkSeed : Digest256)
    (leafFn : UInt64 → Digest256) :
    ∀ (rem level idx : Nat), (quorumAuthPath H pkSeed leafFn rem level idx).length = rem
  | 0, _, _ => rfl
  | rem + 1, level, idx => by
    simp [quorumAuthPath, quorumAuthPath_length H pkSeed leafFn rem (level + 1) (idx / 2)]

/-- Walk a Merkle authentication path upward from `(level, idx, cur)`. -/
def quorumWalkMerklePath (H : List UInt8 → Digest256) (pkSeed : Digest256) :
    Nat → Nat → Digest256 → List Digest256 → Digest256
  | _, _, cur, [] => cur
  | level, idx, cur, sib :: rest =>
    let parentIdx := idx / 2
    let parent :=
      if idx % 2 = 0 then
        quorumMerkleNodeHash H pkSeed (UInt8.ofNat level) (UInt64.ofNat parentIdx) cur sib
      else
        quorumMerkleNodeHash H pkSeed (UInt8.ofNat level) (UInt64.ofNat parentIdx) sib cur
    quorumWalkMerklePath H pkSeed (level + 1) parentIdx parent rest

theorem quorumWalkMerklePath_authPath (H : List UInt8 → Digest256) (pkSeed : Digest256)
    (leafFn : UInt64 → Digest256) :
    ∀ (rem level idx : Nat),
      quorumWalkMerklePath H pkSeed level idx
        (quorumTreeNode H pkSeed leafFn level idx)
        (quorumAuthPath H pkSeed leafFn rem level idx) =
      quorumTreeNode H pkSeed leafFn (level + rem) (idx / 2 ^ rem)
  | 0, level, idx => by
    simp [quorumWalkMerklePath, quorumAuthPath]
  | rem + 1, level, idx => by
    unfold quorumAuthPath quorumWalkMerklePath
    dsimp only
    have hParent :
        (if idx % 2 = 0 then
          quorumMerkleNodeHash H pkSeed (UInt8.ofNat level) (UInt64.ofNat (idx / 2))
            (quorumTreeNode H pkSeed leafFn level idx)
            (quorumTreeNode H pkSeed leafFn level (if idx % 2 = 0 then idx + 1 else idx - 1))
        else
          quorumMerkleNodeHash H pkSeed (UInt8.ofNat level) (UInt64.ofNat (idx / 2))
            (quorumTreeNode H pkSeed leafFn level (if idx % 2 = 0 then idx + 1 else idx - 1))
            (quorumTreeNode H pkSeed leafFn level idx)) =
        quorumTreeNode H pkSeed leafFn (level + 1) (idx / 2) := by
      by_cases hEven : idx % 2 = 0
      · simp only [hEven, ↓reduceIte]
        conv => rhs; unfold quorumTreeNode
        have hL : idx = 2 * (idx / 2) := by omega
        rw [← hL]
      · simp only [hEven, ↓reduceIte]
        conv => rhs; unfold quorumTreeNode
        have hL : idx - 1 = 2 * (idx / 2) := by omega
        have hR : idx - 1 + 1 = idx := by omega
        rw [← hL, hR]
    rw [hParent, quorumWalkMerklePath_authPath H pkSeed leafFn rem (level + 1) (idx / 2)]
    have hLvl : level + 1 + rem = level + (rem + 1) := by omega
    have hDiv : idx / 2 / 2 ^ rem = idx / 2 ^ (rem + 1) := by
      rw [Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm]
    rw [hLvl, hDiv]

/-- Enrolled single-validator `QuorumPublicKey` of tree height `height` over `L` chains. -/
def deriveQuorumValidatorPublicKey (L height : Nat) (H : List UInt8 → Digest256)
    (masterSeed : Digest256) : QuorumPublicKey :=
  let pkSeed := quorumStagePkSeed H masterSeed
  { pkSeed := pkSeed
    root := quorumTreeNode H pkSeed (quorumHonestLeafDigest L H masterSeed) height 0
    height := UInt8.ofNat height }

/-- Step `L` signature chain values forward `3 - d_i` steps to recover candidate chain endpoints. -/
def quorumSigChainEnds (L : Nat) (H : List UInt8 → Digest256)
    (pkSeed : Digest256) (leaf : UInt64) (digits : List (Fin 4))
    (nodes : List Digest256) : List Digest256 :=
  (List.finRange L).map (fun idx =>
    let d := digits.getD idx.1 ⟨0, by decide⟩
    let node := nodes.getD idx.1 0#256
    wotsChainIter (quorumChainStep H pkSeed leaf) idx.1 d.val (3 - d.val) node)

theorem quorumSigChainEnds_length (L : Nat) (H : List UInt8 → Digest256)
    (pkSeed : Digest256) (leaf : UInt64) (digits : List (Fin 4)) (nodes : List Digest256) :
    (quorumSigChainEnds L H pkSeed leaf digits nodes).length = L := by
  simp [quorumSigChainEnds]

/-- Single-validator `QuorumJortsSig` verifier parameterized by `(L, targetSum, digitsOf)`. -/
def verifyQuorumJortsSigAt (L targetSum : Nat) (H : List UInt8 → Digest256)
    (pk : QuorumPublicKey) (digitsOf : Digest256 → List (Fin 4))
    (msg : List UInt8) (sig : QuorumJortsSig) : Bool :=
  let h := pk.height.toNat
  let msgHash := quorumMessageHash H pk sig.leaf msg
  let dig := quorumCounterDigest H msgHash sig.counter
  let digits := digitsOf dig
  decide (sig.leaf.toNat < 2 ^ h) &&
  decide (sig.authPath.length = h) &&
  decide (sig.nodes.length = L) &&
  decide (digits.length = L) &&
  decide (sig.counter.toNat < 2 ^ 16) &&
  decide (((digits.map Fin.val).foldr (· + ·) 0) = targetSum) &&
  let ends := quorumSigChainEnds L H pk.pkSeed sig.leaf digits sig.nodes
  let leafDig := quorumLeafHash H pk.pkSeed sig.leaf ends
  decide (quorumWalkMerklePath H pk.pkSeed 0 sig.leaf.toNat leafDig sig.authPath = pk.root)

/-- Full production 256-bit `QuorumJortsSig` verifier (`v = 128` chains, target sum `S = 192`). -/
def verifyQuorumJortsSig (H : List UInt8 → Digest256)
    (pk : QuorumPublicKey) (msg : List UInt8) (sig : QuorumJortsSig) : Bool :=
  verifyQuorumJortsSigAt quorumWotsChains quorumWotsTargetSum H pk quorumDigitsFromDigest msg sig

private theorem list_getD_eq_getElem_local {α : Type} (xs : List α) (d : α) {i : Nat}
    (hi : i < xs.length) : xs.getD i d = xs[i] := by
  induction xs generalizing i with
  | nil => cases hi
  | cons x rest ih =>
    cases i with
    | zero => rfl
    | succ k => exact ih (Nat.lt_of_succ_lt_succ hi)

private theorem uint8_ofNat_toNat_of_lt {h : Nat} (hLt : h < 256) :
    (UInt8.ofNat h).toNat = h := by
  change (BitVec.ofNat 8 h).toNat = h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hLt]

private theorem uint64_ofNat_toNat_self (x : UInt64) :
    UInt64.ofNat x.toNat = x := by
  apply UInt64.eq_of_toBitVec_eq
  change BitVec.ofNat 64 x.toBitVec.toNat = x.toBitVec
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem quorumSigChainEnds_reference (L : Nat) (H : List UInt8 → Digest256)
    (masterSeed : Digest256) (gLeaf : UInt64) (counter : UInt32)
    (digits : List (Fin 4)) (authPath : List Digest256)
    (hDigLen : digits.length = L) :
    quorumSigChainEnds L H (quorumStagePkSeed H masterSeed) gLeaf digits
      (quorumJortsReferenceSign H masterSeed gLeaf counter digits authPath).nodes =
    quorumHonestChainEnds L H masterSeed gLeaf := by
  subst hDigLen
  unfold quorumSigChainEnds quorumHonestChainEnds quorumJortsReferenceSign
  dsimp only
  apply List.map_congr_left
  intro idx _
  let refNodes := (List.finRange digits.length).map (fun j : Fin digits.length =>
    wotsChainIter (quorumChainStep H (quorumStagePkSeed H masterSeed) gLeaf) j.1 0
      (digits[j.1]'(j.2)).val
      (quorumStageChainSk H masterSeed gLeaf (UInt32.ofNat j.1)))
  have hkRef : idx.1 < refNodes.length := by simp [refNodes, idx.2]
  change wotsChainIter (quorumChainStep H (quorumStagePkSeed H masterSeed) gLeaf) idx.1
      (digits.getD idx.1 ⟨0, by decide⟩).val (3 - (digits.getD idx.1 ⟨0, by decide⟩).val)
      (refNodes.getD idx.1 0#256) =
    wotsChainIter (quorumChainStep H (quorumStagePkSeed H masterSeed) gLeaf) idx.1 0 3
      (quorumStageChainSk H masterSeed gLeaf (UInt32.ofNat idx.1))
  rw [list_getD_eq_getElem_local refNodes 0#256 hkRef,
      list_getD_eq_getElem_local digits _ idx.2]
  simp only [refNodes, List.getElem_map, List.getElem_finRange, Fin.cast_mk]
  let d := digits[idx.1]'(idx.2)
  have hAdd : d.val + (3 - d.val) = 3 := by have := d.isLt; omega
  have hComp := wotsChainIter_add (quorumChainStep H (quorumStagePkSeed H masterSeed) gLeaf)
    idx.1 0 d.val (3 - d.val) (quorumStageChainSk H masterSeed gLeaf (UInt32.ofNat idx.1))
  simp only [Nat.zero_add, hAdd] at hComp
  exact hComp.symm

/-- Honest single-validator `quorumJortsReferenceSign` signatures pass `verifyQuorumJortsSigAt`
    under `deriveQuorumValidatorPublicKey`. -/
theorem quorumJortsReferenceSign_verifies (L targetSum height : Nat)
    (hHeightLt : height < 256)
    (H : List UInt8 → Digest256) (masterSeed : Digest256)
    (digitsOf : Digest256 → List (Fin 4))
    (gLeaf : UInt64) (counter : UInt32) (msg : List UInt8)
    (hLeafLt : gLeaf.toNat < 2 ^ height)
    (hCtrLt : counter.toNat < 2 ^ 16)
    (hDigLen : (digitsOf (quorumCounterDigest H
      (quorumMessageHash H (deriveQuorumValidatorPublicKey L height H masterSeed) gLeaf msg)
      counter)).length = L)
    (hSum : (((digitsOf (quorumCounterDigest H
      (quorumMessageHash H (deriveQuorumValidatorPublicKey L height H masterSeed) gLeaf msg)
      counter)).map Fin.val).foldr (· + ·) 0) = targetSum) :
    let pk := deriveQuorumValidatorPublicKey L height H masterSeed
    let digits := digitsOf (quorumCounterDigest H (quorumMessageHash H pk gLeaf msg) counter)
    let authPath := quorumAuthPath H pk.pkSeed (quorumHonestLeafDigest L H masterSeed) height 0 gLeaf.toNat
    verifyQuorumJortsSigAt L targetSum H pk digitsOf msg
      (quorumJortsReferenceSign H masterSeed gLeaf counter digits authPath) = true := by
  intro pk digits authPath
  have hDigLen' : digits.length = L := hDigLen
  have hPkH : pk.height.toNat = height := uint8_ofNat_toNat_of_lt hHeightLt
  have hPkS : pk.pkSeed = quorumStagePkSeed H masterSeed := rfl
  have hPathLen : authPath.length = height :=
    quorumAuthPath_length H pk.pkSeed (quorumHonestLeafDigest L H masterSeed) height 0 gLeaf.toNat
  have hNodesLen :
      (quorumJortsReferenceSign H masterSeed gLeaf counter digits authPath).nodes.length = L := by
    simp [quorumJortsReferenceSign, hDigLen']
  unfold verifyQuorumJortsSigAt
  dsimp only [quorumJortsReferenceSign]
  rw [hPkH]
  have hEnds :
      quorumSigChainEnds L H pk.pkSeed gLeaf digits
        (quorumJortsReferenceSign H masterSeed gLeaf counter digits authPath).nodes =
      quorumHonestChainEnds L H masterSeed gLeaf := by
    rw [hPkS]
    exact quorumSigChainEnds_reference L H masterSeed gLeaf counter digits authPath hDigLen
  have hWalk :
      quorumWalkMerklePath H pk.pkSeed 0 gLeaf.toNat
        (quorumLeafHash H pk.pkSeed gLeaf
          (quorumSigChainEnds L H pk.pkSeed gLeaf digits
            (quorumJortsReferenceSign H masterSeed gLeaf counter digits authPath).nodes))
        authPath = pk.root := by
    rw [hEnds]
    have hLeafNode :
        quorumLeafHash H pk.pkSeed gLeaf (quorumHonestChainEnds L H masterSeed gLeaf) =
        quorumTreeNode H pk.pkSeed (quorumHonestLeafDigest L H masterSeed) 0 gLeaf.toNat := by
      unfold quorumTreeNode quorumHonestLeafDigest
      rw [uint64_ofNat_toNat_self, hPkS]
    rw [hLeafNode, quorumWalkMerklePath_authPath]
    simp [Nat.zero_add, Nat.div_eq_of_lt hLeafLt, pk, deriveQuorumValidatorPublicKey]
  have hLeafCheck : decide (gLeaf.toNat < 2 ^ height) = true := decide_eq_true hLeafLt
  have hPathCheck : decide (authPath.length = height) = true := decide_eq_true hPathLen
  have hNodesCheck :
      decide ((quorumJortsReferenceSign H masterSeed gLeaf counter digits authPath).nodes.length = L) =
        true := decide_eq_true hNodesLen
  have hDigCheck : decide (digits.length = L) = true := decide_eq_true hDigLen
  have hCtrCheck : decide (counter.toNat < 2 ^ 16) = true := decide_eq_true hCtrLt
  have hSumCheck : decide (((digits.map Fin.val).foldr (· + ·) 0) = targetSum) = true :=
    decide_eq_true hSum
  have hWalkCheck :
      decide (quorumWalkMerklePath H pk.pkSeed 0 gLeaf.toNat
        (quorumLeafHash H pk.pkSeed gLeaf
          (quorumSigChainEnds L H pk.pkSeed gLeaf digits
            (quorumJortsReferenceSign H masterSeed gLeaf counter digits authPath).nodes))
        authPath = pk.root) = true := decide_eq_true hWalk
  change (decide (gLeaf.toNat < 2 ^ height) &&
    decide (authPath.length = height) &&
    decide ((quorumJortsReferenceSign H masterSeed gLeaf counter digits authPath).nodes.length = L) &&
    decide (digits.length = L) &&
    decide (counter.toNat < 2 ^ 16) &&
    decide (((digits.map Fin.val).foldr (· + ·) 0) = targetSum) &&
    decide (quorumWalkMerklePath H pk.pkSeed 0 gLeaf.toNat
      (quorumLeafHash H pk.pkSeed gLeaf
        (quorumSigChainEnds L H pk.pkSeed gLeaf digits
          (quorumJortsReferenceSign H masterSeed gLeaf counter digits authPath).nodes))
      authPath = pk.root)) = true
  rw [hLeafCheck, hPathCheck, hNodesCheck, hDigCheck, hCtrCheck, hSumCheck, hWalkCheck]
  rfl

/-! ### Constructive `PSum` Collision Extractors for Chain, Leaf & Merkle Verification -/

private theorem pow256_8_gt_64_local : 64 < 256 ^ 8 :=
  calc 64 < 256 ^ 1 := by decide
    _ ≤ 256 ^ 8 := Nat.pow_le_pow_right (by decide) (by decide)

private theorem quorumEncodeFramed3_injective
    (domain : ByteArray) (hd : domain.data.toList.length < 256 ^ 8)
    {a₁ b₁ c₁ a₂ b₂ c₂ : List UInt8}
    (ha₁ : a₁.length < 256 ^ 8) (hb₁ : b₁.length < 256 ^ 8) (hc₁ : c₁.length < 256 ^ 8)
    (ha₂ : a₂.length < 256 ^ 8) (hb₂ : b₂.length < 256 ^ 8) (hc₂ : c₂.length < 256 ^ 8)
    (hEq : quorumEncodeFramed domain [a₁, b₁, c₁] =
           quorumEncodeFramed domain [a₂, b₂, c₂]) :
    a₁ = a₂ ∧ b₁ = b₂ ∧ c₁ = c₂ := by
  simp only [quorumEncodeFramed, quorumFrameFields] at hEq
  obtain ⟨_, r1⟩ := quorumFrameField_prefix_inj hd hd hEq
  obtain ⟨ea, r2⟩ := quorumFrameField_prefix_inj ha₁ ha₂ r1
  obtain ⟨eb, r3⟩ := quorumFrameField_prefix_inj hb₁ hb₂ r2
  obtain ⟨ec, _⟩ := quorumFrameField_prefix_inj hc₁ hc₂ r3
  exact ⟨ea, eb, ec⟩

private theorem quorumEncodeFramed5_injective
    (domain : ByteArray) (hd : domain.data.toList.length < 256 ^ 8)
    {a₁ b₁ c₁ d₁ e₁ a₂ b₂ c₂ d₂ e₂ : List UInt8}
    (ha₁ : a₁.length < 256 ^ 8) (hb₁ : b₁.length < 256 ^ 8) (hc₁ : c₁.length < 256 ^ 8)
    (hd₁ : d₁.length < 256 ^ 8) (he₁ : e₁.length < 256 ^ 8)
    (ha₂ : a₂.length < 256 ^ 8) (hb₂ : b₂.length < 256 ^ 8) (hc₂ : c₂.length < 256 ^ 8)
    (hd₂ : d₂.length < 256 ^ 8) (he₂ : e₂.length < 256 ^ 8)
    (hEq : quorumEncodeFramed domain [a₁, b₁, c₁, d₁, e₁] =
           quorumEncodeFramed domain [a₂, b₂, c₂, d₂, e₂]) :
    a₁ = a₂ ∧ b₁ = b₂ ∧ c₁ = c₂ ∧ d₁ = d₂ ∧ e₁ = e₂ := by
  simp only [quorumEncodeFramed, quorumFrameFields] at hEq
  obtain ⟨_, r1⟩ := quorumFrameField_prefix_inj hd hd hEq
  obtain ⟨ea, r2⟩ := quorumFrameField_prefix_inj ha₁ ha₂ r1
  obtain ⟨eb, r3⟩ := quorumFrameField_prefix_inj hb₁ hb₂ r2
  obtain ⟨ec, r4⟩ := quorumFrameField_prefix_inj hc₁ hc₂ r3
  obtain ⟨ed, r5⟩ := quorumFrameField_prefix_inj hd₁ hd₂ r4
  obtain ⟨ee, _⟩ := quorumFrameField_prefix_inj he₁ he₂ r5
  exact ⟨ea, eb, ec, ed, ee⟩

private theorem quorumChainPreimage_ne
    (pkSeed : Digest256) (adrs : List UInt8) (nodeA nodeB : Digest256)
    (hAdrs : adrs.length = 16) (hNe : nodeA ≠ nodeB) :
    quorumEncodeFramed quorumChainTag [encodeDigest256 pkSeed, adrs, encodeDigest256 nodeA] ≠
      quorumEncodeFramed quorumChainTag [encodeDigest256 pkSeed, adrs, encodeDigest256 nodeB] := by
  intro hEq
  have hTagLt : quorumChainTag.data.toList.length < 256 ^ 8 :=
    Nat.lt_trans (by decide : quorumChainTag.data.toList.length < 64) pow256_8_gt_64_local
  have hLen32 : ∀ d, (encodeDigest256 d).length < 256 ^ 8 := fun d => by
    rw [encodeDigest256_length]
    exact Nat.lt_trans (by decide : 32 < 64) pow256_8_gt_64_local
  have hAdrsLt : adrs.length < 256 ^ 8 := by
    rw [hAdrs]
    exact Nat.lt_trans (by decide : 16 < 64) pow256_8_gt_64_local
  obtain ⟨_, _, hNodeEnc⟩ :=
    quorumEncodeFramed3_injective quorumChainTag hTagLt
      (hLen32 pkSeed) hAdrsLt (hLen32 nodeA)
      (hLen32 pkSeed) hAdrsLt (hLen32 nodeB) hEq
  exact hNe (encodeDigest256_injective hNodeEnc)

/-- Convert any `WotsChainCollisionWitness (quorumChainStep H pkSeed leaf) 4` into an explicit
    framed byte-level `HashCollision256 H` (`0 Classical.choice`). -/
def wotsChainCollision_to_hashCollision256 (H : List UInt8 → Digest256)
    (pkSeed : Digest256) (leaf : UInt64)
    (w : WotsChainCollisionWitness (quorumChainStep H pkSeed leaf) 4) :
    HashCollision256 H :=
  { preA := quorumEncodeFramed quorumChainTag
      [encodeDigest256 pkSeed,
       encodeNatBeBytes 8 leaf.toNat ++ encodeNatBeBytes 4 w.chainIdx ++ encodeNatBeBytes 4 w.stepPos,
       encodeDigest256 w.nodeA]
    preB := quorumEncodeFramed quorumChainTag
      [encodeDigest256 pkSeed,
       encodeNatBeBytes 8 leaf.toNat ++ encodeNatBeBytes 4 w.chainIdx ++ encodeNatBeBytes 4 w.stepPos,
       encodeDigest256 w.nodeB]
    distinct := quorumChainPreimage_ne pkSeed
      (encodeNatBeBytes 8 leaf.toNat ++ encodeNatBeBytes 4 w.chainIdx ++ encodeNatBeBytes 4 w.stepPos)
      w.nodeA w.nodeB (by simp [encodeNatBeBytes_length]) w.nodes_ne
    same_digest := w.step_eq }

private theorem flatMap_encodeDigest256_injective :
    ∀ {xs ys : List Digest256},
      xs.length = ys.length →
      xs.flatMap encodeDigest256 = ys.flatMap encodeDigest256 →
      xs = ys
  | [], [], _, _ => rfl
  | x :: xs, y :: ys, hLen, hEq => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hLen
    simp only [List.flatMap_cons] at hEq
    have h32 : (encodeDigest256 x).length = (encodeDigest256 y).length := by
      rw [encodeDigest256_length, encodeDigest256_length]
    obtain ⟨hHead, hTail⟩ := List.append_inj hEq h32
    rw [encodeDigest256_injective hHead, flatMap_encodeDigest256_injective hLen hTail]

private theorem quorumLeafPreimage_ne
    (pkSeed : Digest256) (leaf : UInt64) (ends₁ ends₂ : List Digest256)
    (hLenEq : ends₁.length = ends₂.length)
    (hLenBound : 32 * ends₁.length < 256 ^ 8)
    (hNe : ends₁ ≠ ends₂) :
    quorumEncodeFramed quorumLeafTag
      [encodeDigest256 pkSeed, encodeNatBeBytes 8 leaf.toNat, ends₁.flatMap encodeDigest256] ≠
    quorumEncodeFramed quorumLeafTag
      [encodeDigest256 pkSeed, encodeNatBeBytes 8 leaf.toNat, ends₂.flatMap encodeDigest256] := by
  intro hPreEq
  have hFlatLen : ∀ zs : List Digest256, (zs.flatMap encodeDigest256).length = 32 * zs.length := by
    intro zs
    induction zs with
    | nil => simp
    | cons z rest ih =>
      simp only [List.flatMap_cons, List.length_append, encodeDigest256_length, ih, List.length_cons]
      omega
  have hTagLt : quorumLeafTag.data.toList.length < 256 ^ 8 :=
    Nat.lt_trans (by decide : quorumLeafTag.data.toList.length < 64) pow256_8_gt_64_local
  have h32 : (encodeDigest256 pkSeed).length < 256 ^ 8 := by
    rw [encodeDigest256_length]
    exact Nat.lt_trans (by decide : 32 < 64) pow256_8_gt_64_local
  have h8 : (encodeNatBeBytes 8 leaf.toNat).length < 256 ^ 8 := by
    rw [encodeNatBeBytes_length]
    exact Nat.lt_trans (by decide : 8 < 64) pow256_8_gt_64_local
  have hFl1 : (ends₁.flatMap encodeDigest256).length < 256 ^ 8 := by
    rw [hFlatLen]; exact hLenBound
  have hFl2 : (ends₂.flatMap encodeDigest256).length < 256 ^ 8 := by
    rw [hFlatLen, ← hLenEq]; exact hLenBound
  obtain ⟨_, _, hEndsEnc⟩ :=
    quorumEncodeFramed3_injective quorumLeafTag hTagLt
      h32 h8 hFl1 h32 h8 hFl2 hPreEq
  exact hNe (flatMap_encodeDigest256_injective hLenEq hEndsEnc)

/-- Constructive leaf-hash collision extractor when `ends₁ ≠ ends₂` of equal length `L < 2^56`
    hash to the same `quorumLeafHash`. -/
def extractQuorumLeafHashCollision (H : List UInt8 → Digest256)
    (pkSeed : Digest256) (leaf : UInt64) (ends₁ ends₂ : List Digest256)
    (hLenEq : ends₁.length = ends₂.length)
    (hLenBound : 32 * ends₁.length < 256 ^ 8)
    (hNe : ends₁ ≠ ends₂)
    (hHash : quorumLeafHash H pkSeed leaf ends₁ = quorumLeafHash H pkSeed leaf ends₂) :
    HashCollision256 H :=
  { preA := quorumEncodeFramed quorumLeafTag
      [encodeDigest256 pkSeed, encodeNatBeBytes 8 leaf.toNat, ends₁.flatMap encodeDigest256]
    preB := quorumEncodeFramed quorumLeafTag
      [encodeDigest256 pkSeed, encodeNatBeBytes 8 leaf.toNat, ends₂.flatMap encodeDigest256]
    distinct := quorumLeafPreimage_ne pkSeed leaf ends₁ ends₂ hLenEq hLenBound hNe
    same_digest := hHash }

private theorem quorumNodePreimage_ne
    (pkSeed : Digest256) (lvl : UInt8) (idx : UInt64)
    (l₁ r₁ l₂ r₂ : Digest256)
    (hNe : l₁ ≠ l₂ ∨ r₁ ≠ r₂) :
    quorumEncodeFramed quorumNodeTag
      [encodeDigest256 pkSeed, [lvl], encodeNatBeBytes 8 idx.toNat,
       encodeDigest256 l₁, encodeDigest256 r₁] ≠
    quorumEncodeFramed quorumNodeTag
      [encodeDigest256 pkSeed, [lvl], encodeNatBeBytes 8 idx.toNat,
       encodeDigest256 l₂, encodeDigest256 r₂] := by
  intro hPreEq
  have hTagLt : quorumNodeTag.data.toList.length < 256 ^ 8 :=
    Nat.lt_trans (by decide : quorumNodeTag.data.toList.length < 64) pow256_8_gt_64_local
  have h32 : ∀ d, (encodeDigest256 d).length < 256 ^ 8 := fun d => by
    rw [encodeDigest256_length]
    exact Nat.lt_trans (by decide : 32 < 64) pow256_8_gt_64_local
  have h1 : ([lvl] : List UInt8).length < 256 ^ 8 :=
    Nat.lt_trans (by decide : 1 < 64) pow256_8_gt_64_local
  have h8 : (encodeNatBeBytes 8 idx.toNat).length < 256 ^ 8 := by
    rw [encodeNatBeBytes_length]
    exact Nat.lt_trans (by decide : 8 < 64) pow256_8_gt_64_local
  obtain ⟨_, _, _, hL_enc, hR_enc⟩ :=
    quorumEncodeFramed5_injective quorumNodeTag hTagLt
      (h32 pkSeed) h1 h8 (h32 l₁) (h32 r₁)
      (h32 pkSeed) h1 h8 (h32 l₂) (h32 r₂) hPreEq
  rcases hNe with hL | hR
  · exact hL (encodeDigest256_injective hL_enc)
  · exact hR (encodeDigest256_injective hR_enc)

/-- Constructive internal Merkle node collision extractor (`(l₁, r₁) ≠ (l₂, r₂)`). -/
def extractQuorumNodeHashCollision (H : List UInt8 → Digest256)
    (pkSeed : Digest256) (lvl : UInt8) (idx : UInt64)
    (l₁ r₁ l₂ r₂ : Digest256)
    (hNe : l₁ ≠ l₂ ∨ r₁ ≠ r₂)
    (hHash : quorumMerkleNodeHash H pkSeed lvl idx l₁ r₁ =
             quorumMerkleNodeHash H pkSeed lvl idx l₂ r₂) :
    HashCollision256 H :=
  { preA := quorumEncodeFramed quorumNodeTag
      [encodeDigest256 pkSeed, [lvl], encodeNatBeBytes 8 idx.toNat,
       encodeDigest256 l₁, encodeDigest256 r₁]
    preB := quorumEncodeFramed quorumNodeTag
      [encodeDigest256 pkSeed, [lvl], encodeNatBeBytes 8 idx.toNat,
       encodeDigest256 l₂, encodeDigest256 r₂]
    distinct := quorumNodePreimage_ne pkSeed lvl idx l₁ r₁ l₂ r₂ hNe
    same_digest := hHash }

/-- Constructive Merkle path collision extractor (`0 Classical.choice`):
    Whenever `cur ≠ quorumTreeNode H pkSeed leafFn level idx` walks `path` (`path.length = rem`)
    to `quorumTreeNode H pkSeed leafFn (level + rem) (idx / 2 ^ rem)`, extracts the exact level
    where `quorumMerkleNodeHash` collided! -/
def extractQuorumMerkleWalkCollision (H : List UInt8 → Digest256) (pkSeed : Digest256)
    (leafFn : UInt64 → Digest256) :
    ∀ (path : List Digest256) (level idx : Nat) (cur : Digest256),
      cur ≠ quorumTreeNode H pkSeed leafFn level idx →
      quorumWalkMerklePath H pkSeed level idx cur path =
        quorumTreeNode H pkSeed leafFn (level + path.length) (idx / 2 ^ path.length) →
      HashCollision256 H
  | [], level, idx, cur, hNe, hWalk => by
    simp only [quorumWalkMerklePath, List.length_nil, Nat.add_zero, Nat.pow_zero, Nat.div_one] at hWalk
    exact False.elim (hNe hWalk)
  | sib :: rest, level, idx, cur, hNe, hWalk =>
    let parentIdx := idx / 2
    let parent :=
      if idx % 2 = 0 then
        quorumMerkleNodeHash H pkSeed (UInt8.ofNat level) (UInt64.ofNat parentIdx) cur sib
      else
        quorumMerkleNodeHash H pkSeed (UInt8.ofNat level) (UInt64.ofNat parentIdx) sib cur
    let honestParent := quorumTreeNode H pkSeed leafFn (level + 1) parentIdx
    if hParEq : parent = honestParent then
      if hEven : idx % 2 = 0 then
        extractQuorumNodeHashCollision H pkSeed (UInt8.ofNat level) (UInt64.ofNat parentIdx)
          cur sib
          (quorumTreeNode H pkSeed leafFn level (2 * parentIdx))
          (quorumTreeNode H pkSeed leafFn level (2 * parentIdx + 1))
          (.inl (by
            have hIdx : 2 * parentIdx = idx := by omega
            rw [hIdx]; exact hNe))
          (by
            have hP : parent = quorumMerkleNodeHash H pkSeed (UInt8.ofNat level)
                (UInt64.ofNat parentIdx) cur sib := by simp [parent, hEven]
            rw [← hP]; exact hParEq)
      else
        extractQuorumNodeHashCollision H pkSeed (UInt8.ofNat level) (UInt64.ofNat parentIdx)
          sib cur
          (quorumTreeNode H pkSeed leafFn level (2 * parentIdx))
          (quorumTreeNode H pkSeed leafFn level (2 * parentIdx + 1))
          (.inr (by
            have hIdx : 2 * parentIdx + 1 = idx := by omega
            rw [hIdx]; exact hNe))
          (by
            have hP : parent = quorumMerkleNodeHash H pkSeed (UInt8.ofNat level)
                (UInt64.ofNat parentIdx) sib cur := by simp [parent, hEven]
            rw [← hP]; exact hParEq)
    else
      extractQuorumMerkleWalkCollision H pkSeed leafFn rest (level + 1) parentIdx parent hParEq
        (by
          have hW := hWalk
          unfold quorumWalkMerklePath at hW
          dsimp only [List.length_cons] at hW
          have hLvl : level + (rest.length + 1) = level + 1 + rest.length := by omega
          have hDiv : idx / 2 ^ (rest.length + 1) = parentIdx / 2 ^ rest.length := by
            dsimp only [parentIdx]
            rw [Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm]
          rw [hLvl, hDiv] at hW
          exact hW)

private def extractChainClawLocal (F : Nat → Nat → Digest256 → Digest256) (chainIdx : Nat) :
    (start rem : Nat) → (a b : Digest256) →
    start + rem = 3 →
    a ≠ b →
    wotsChainIter F chainIdx start rem a = wotsChainIter F chainIdx start rem b →
    WotsChainCollisionWitness F 4
  | _, 0, _, _, _, hNe, hEq => False.elim (hNe hEq)
  | start, rem + 1, a, b, hBound, hNe, hEq =>
    if hStep : F chainIdx start a = F chainIdx start b then
      { chainIdx := chainIdx
        stepPos := start
        step_lt := by omega
        nodeA := a
        nodeB := b
        nodes_ne := hNe
        step_eq := hStep }
    else
      extractChainClawLocal F chainIdx (start + 1) rem
        (F chainIdx start a) (F chainIdx start b) (by omega) hStep hEq

private def findListDiffAt :
    (xs ys : List Digest256) → (off : Nat) →
    xs.length = ys.length →
    PSum (xs = ys) { k : Nat // k < xs.length ∧ xs.getD k 0#256 ≠ ys.getD k 0#256 }
  | [], [], _, _ => .inl rfl
  | x :: xs, y :: ys, off, hLen =>
    if hxy : x = y then
      match findListDiffAt xs ys (off + 1) (Nat.succ.inj hLen) with
      | .inl hRest => .inl (by subst hxy hRest; rfl)
      | .inr ⟨k, hkLt, hkNe⟩ =>
        .inr ⟨k + 1, Nat.succ_lt_succ hkLt, hkNe⟩
    else
      .inr ⟨0, Nat.zero_lt_succ _, hxy⟩

/-- **Constructive Single-Validator Verification Extractor
    (`verifyQuorumJortsSigAt_extract_reference_or_collision`, `0 Classical.choice`)**:
    For ANY signature `sig` accepted by `verifyQuorumJortsSigAt` under the enrolled
    single-validator key `deriveQuorumValidatorPublicKey L height H masterSeed`
    (`height < 256`, `32 * L < 256 ^ 8`), constructively returns EITHER:
    - `.inl`: `sig.nodes` equals the exact single-validator reference chain vector
      `(quorumJortsReferenceSign H masterSeed sig.leaf sig.counter digits sig.authPath).nodes`, OR
    - `.inr (.inl w)`: an explicit WOTS+C step collision `WotsChainCollisionWitness`, OR
    - `.inr (.inr c)`: an explicit Merkle/leaf 256-bit `HashCollision256 H`! -/
def verifyQuorumJortsSigAt_extract_reference_or_collision (L targetSum height : Nat)
    (hHeightLt : height < 256) (hChainBound : 32 * L < 256 ^ 8)
    (H : List UInt8 → Digest256) (masterSeed : Digest256)
    (digitsOf : Digest256 → List (Fin 4))
    (msg : List UInt8) (sig : QuorumJortsSig)
    (hAcc : verifyQuorumJortsSigAt L targetSum H
      (deriveQuorumValidatorPublicKey L height H masterSeed) digitsOf msg sig = true) :
    let pk := deriveQuorumValidatorPublicKey L height H masterSeed
    let digits := digitsOf (quorumCounterDigest H (quorumMessageHash H pk sig.leaf msg) sig.counter)
    let refNodes := (quorumJortsReferenceSign H masterSeed sig.leaf sig.counter digits sig.authPath).nodes
    PSum (sig.nodes = refNodes)
      (PSum (WotsChainCollisionWitness (quorumChainStep H pk.pkSeed sig.leaf) 4)
            (HashCollision256 H)) :=
  let pk := deriveQuorumValidatorPublicKey L height H masterSeed
  let digits := digitsOf (quorumCounterDigest H (quorumMessageHash H pk sig.leaf msg) sig.counter)
  let refNodes := (quorumJortsReferenceSign H masterSeed sig.leaf sig.counter digits sig.authPath).nodes
  have hPkH : pk.height.toNat = height := uint8_ofNat_toNat_of_lt hHeightLt
  have hUnpack :
      sig.leaf.toNat < 2 ^ height ∧
      sig.authPath.length = height ∧
      sig.nodes.length = L ∧
      digits.length = L ∧
      quorumWalkMerklePath H pk.pkSeed 0 sig.leaf.toNat
        (quorumLeafHash H pk.pkSeed sig.leaf
          (quorumSigChainEnds L H pk.pkSeed sig.leaf digits sig.nodes))
        sig.authPath = pk.root := by
    unfold verifyQuorumJortsSigAt at hAcc
    dsimp only at hAcc
    rcases Bool.and_eq_true_iff.mp hAcc with ⟨h16, hWalkB⟩
    rcases Bool.and_eq_true_iff.mp h16 with ⟨h15, _⟩
    rcases Bool.and_eq_true_iff.mp h15 with ⟨h14, _⟩
    rcases Bool.and_eq_true_iff.mp h14 with ⟨h13, hDigB⟩
    rcases Bool.and_eq_true_iff.mp h13 with ⟨h12, hNodesB⟩
    rcases Bool.and_eq_true_iff.mp h12 with ⟨hLeafB, hPathB⟩
    exact ⟨hPkH ▸ of_decide_eq_true hLeafB,
           hPkH ▸ of_decide_eq_true hPathB,
           of_decide_eq_true hNodesB,
           of_decide_eq_true hDigB,
           of_decide_eq_true hWalkB⟩
  let sigEnds := quorumSigChainEnds L H pk.pkSeed sig.leaf digits sig.nodes
  let honEnds := quorumHonestChainEnds L H masterSeed sig.leaf
  let sigLeafDig := quorumLeafHash H pk.pkSeed sig.leaf sigEnds
  let honLeafDig := quorumTreeNode H pk.pkSeed (quorumHonestLeafDigest L H masterSeed) 0 sig.leaf.toNat
  if hLeafEq : sigLeafDig = honLeafDig then
    have hLeafHashEq :
        quorumLeafHash H pk.pkSeed sig.leaf sigEnds =
        quorumLeafHash H pk.pkSeed sig.leaf honEnds := by
      have hHonDef : honLeafDig = quorumLeafHash H pk.pkSeed sig.leaf honEnds := by
        dsimp only [honLeafDig, quorumTreeNode, quorumHonestLeafDigest, pk,
          deriveQuorumValidatorPublicKey, honEnds]
        rw [uint64_ofNat_toNat_self]
      exact hLeafEq.trans hHonDef
    if hEndsEq : sigEnds = honEnds then
      have hRefLen : refNodes.length = L := by
        simp [refNodes, quorumJortsReferenceSign, hUnpack.2.2.2.1]
      match findListDiffAt sig.nodes refNodes 0 (hUnpack.2.2.1.trans hRefLen.symm) with
      | .inl hNodesEq => .inl hNodesEq
      | .inr ⟨k, hkLtSig, hkNe⟩ =>
        have hkLtL : k < L := hUnpack.2.2.1 ▸ hkLtSig
        have hEndK : sigEnds[k]'(by rw [quorumSigChainEnds_length]; exact hkLtL) =
            honEnds[k]'(by rw [quorumHonestChainEnds_length]; exact hkLtL) := by
          simp [hEndsEq]
        have hRefEnds : quorumSigChainEnds L H pk.pkSeed sig.leaf digits refNodes = honEnds :=
          quorumSigChainEnds_reference L H masterSeed sig.leaf sig.counter digits sig.authPath
            hUnpack.2.2.2.1
        have hIterEq :
            wotsChainIter (quorumChainStep H pk.pkSeed sig.leaf) k
              (digits.getD k ⟨0, by decide⟩).val (3 - (digits.getD k ⟨0, by decide⟩).val)
              (sig.nodes.getD k 0#256) =
            wotsChainIter (quorumChainStep H pk.pkSeed sig.leaf) k
              (digits.getD k ⟨0, by decide⟩).val (3 - (digits.getD k ⟨0, by decide⟩).val)
              (refNodes.getD k 0#256) := by
          have h1 : sigEnds[k]'(by rw [quorumSigChainEnds_length]; exact hkLtL) =
              wotsChainIter (quorumChainStep H pk.pkSeed sig.leaf) k
                (digits.getD k ⟨0, by decide⟩).val (3 - (digits.getD k ⟨0, by decide⟩).val)
                (sig.nodes.getD k 0#256) := by
            simp [sigEnds, quorumSigChainEnds]
          have h2 : (quorumSigChainEnds L H pk.pkSeed sig.leaf digits refNodes)[k]'(by
                rw [quorumSigChainEnds_length]; exact hkLtL) =
              wotsChainIter (quorumChainStep H pk.pkSeed sig.leaf) k
                (digits.getD k ⟨0, by decide⟩).val (3 - (digits.getD k ⟨0, by decide⟩).val)
                (refNodes.getD k 0#256) := by
            simp [quorumSigChainEnds]
          rw [← h1, ← h2]
          simp [hEndsEq, hRefEnds]
        have hdLe : (digits.getD k ⟨0, by decide⟩).val ≤ 3 := by
          have := (digits.getD k ⟨0, by decide⟩).isLt; omega
        .inr (.inl (extractChainClawLocal (quorumChainStep H pk.pkSeed sig.leaf) k
          (digits.getD k ⟨0, by decide⟩).val (3 - (digits.getD k ⟨0, by decide⟩).val)
          (sig.nodes.getD k 0#256) (refNodes.getD k 0#256) (by omega) hkNe hIterEq))
    else
      .inr (.inr (extractQuorumLeafHashCollision H pk.pkSeed sig.leaf sigEnds honEnds
        (by rw [quorumSigChainEnds_length, quorumHonestChainEnds_length])
        (by rw [quorumSigChainEnds_length]; exact hChainBound)
        hEndsEq hLeafHashEq))
  else
    .inr (.inr (extractQuorumMerkleWalkCollision H pk.pkSeed
      (quorumHonestLeafDigest L H masterSeed) sig.authPath 0 sig.leaf.toNat sigLeafDig hLeafEq
      (by
        rw [Nat.zero_add, hUnpack.2.1, Nat.div_eq_of_lt hUnpack.1]
        exact hUnpack.2.2.2.2)))

/-! ## §2. Per-Custodian `LockstepSim` & `ForwardSim` to `CompleteMediationBoundary` -/

/-- Pre-stepped `GF(2^128)²` (`TowerElem 7 × TowerElem 7`) Shamir share opening released by a
    single custodian `party : Fin n` upon consuming its one-time `Custody.Vault.active` handle. -/
structure ShamirCustodianShareOpening (n L : Nat) where
  party : Fin n
  intent : Custody.Intent
  epoch : UInt64
  counter : UInt32
  evalPoint : TowerElem 7
  chainShares : Fin L → Option (TowerElem 7 × TowerElem 7)

/-- Compute custodian `party`'s pre-stepped `GF(2^128)²` Shamir share opening at `evalPt`. -/
def computeShamirCustodianOpening {n L d : Nat}
    (H : List UInt8 → Digest256) (masterSeed : Digest256)
    (polyTape : UInt64 → PreSteppedDigest256ShamirTape d L)
    (evalPt : TowerElem 7) (party : Fin n)
    (r : Custody.Intent) (counter : UInt32)
    (digits : Fin L → Fin 4) : ShamirCustodianShareOpening n L :=
  let gLeaf := UInt64.ofNat r.leaf
  let pkSeed := quorumStagePkSeed H masterSeed
  { party := party
    intent := r
    epoch := gLeaf
    counter := counter
    evalPoint := evalPt
    chainShares := fun i =>
      if hStep : (digits i).val < 3 then
        let k : Fin 3 := ⟨(digits i).val, hStep⟩
        let sk₀ := quorumStageChainSk H masterSeed gLeaf (UInt32.ofNat i.1)
        let trueNode := wotsChainIter (quorumChainStep H pkSeed gLeaf) i.1 0 (digits i).val sk₀
        let (lo, hi) := splitDigest256Tower128 trueNode
        some (RoundPoly.evalCoeffs (lo :: (polyTape gLeaf i k).1.1) evalPt,
              RoundPoly.evalCoeffs (hi :: (polyTape gLeaf i k).2.1) evalPt)
      else
        none }

/-- One-time complete-mediation share release on `Custody.Vault`:
    enforces exact anchor continuity, poisons on mismatch, and atomically burns `v.active = some r`
    into `r :: v.attempted` before emitting `ShamirCustodianShareOpening` (matching
    `Custody.release`'s vault transition in `CompleteMediationBoundary`). -/
def releaseShamirShareFromVault {n L d : Nat}
    (H : List UInt8 → Digest256) (masterSeed : Digest256)
    (polyTape : UInt64 → PreSteppedDigest256ShamirTape d L)
    (evalPt : TowerElem 7) (party : Fin n)
    (anchor : Nat) (v : Custody.Vault)
    (r : Custody.Intent) (counter : UInt32) (digits : Fin L → Fin 4) :
    Custody.Vault × Option (ShamirCustodianShareOpening n L) :=
  if v.poisoned || decide (v.durable.anchor ≠ anchor) then
    ({ v with poisoned := true, active := none }, none)
  else if v.active = some r then
    ({ v with active := none, attempted := r :: v.attempted },
     some (computeShamirCustodianOpening H masterSeed polyTape evalPt party r counter digits))
  else
    (v, none)

theorem releaseShamirShareFromVault_safe {n L d : Nat}
    (H : List UInt8 → Digest256) (masterSeed : Digest256)
    (polyTape : UInt64 → PreSteppedDigest256ShamirTape d L)
    (evalPt : TowerElem 7) (party : Fin n)
    (policy : Custody.RoundPolicy) (cap anchor : Nat) (v : Custody.Vault)
    (r : Custody.Intent) (counter : UInt32) (digits : Fin L → Fin 4)
    (hSafe : Custody.Safe policy cap v) :
    Custody.Safe policy cap
      (releaseShamirShareFromVault H masterSeed polyTape evalPt party anchor v r counter digits).1 := by
  unfold releaseShamirShareFromVault
  split
  · exact ⟨hSafe.budget, hSafe.accounting, hSafe.past, hSafe.uniqueLeaf, hSafe.approved,
      (fun _ he => by cases he), hSafe.attemptedBurned, (fun _ he => by cases he),
      hSafe.attemptedNodup⟩
  · split
    next ha =>
      refine ⟨hSafe.budget, hSafe.accounting, hSafe.past, hSafe.uniqueLeaf, hSafe.approved,
        (fun _ he => by cases he), ?_, (fun _ he => by cases he), ?_⟩
      · intro s hs
        rcases List.mem_cons.mp hs with hs | hs
        · subst s; exact hSafe.activeBurned r ha
        · exact hSafe.attemptedBurned s hs
      · exact List.nodup_cons.mpr ⟨hSafe.activeFresh r ha, hSafe.attemptedNodup⟩
    next => exact hSafe

theorem releaseShamirShareFromVault_replay_rejected {n L d : Nat}
    (H : List UInt8 → Digest256) (masterSeed : Digest256)
    (polyTape : UInt64 → PreSteppedDigest256ShamirTape d L)
    (evalPt : TowerElem 7) (party : Fin n)
    (anchor : Nat) (v : Custody.Vault)
    (r : Custody.Intent) (counter₁ counter₂ : UInt32) (digits₁ digits₂ : Fin L → Fin 4)
    (op : ShamirCustodianShareOpening n L)
    (hRel : (releaseShamirShareFromVault H masterSeed polyTape evalPt party anchor v r
      counter₁ digits₁).2 = some op) :
    (releaseShamirShareFromVault H masterSeed polyTape evalPt party anchor
      (releaseShamirShareFromVault H masterSeed polyTape evalPt party anchor v r counter₁ digits₁).1
      r counter₂ digits₂).2 = none := by
  generalize hV1 : (releaseShamirShareFromVault H masterSeed polyTape evalPt party anchor v r
    counter₁ digits₁) = res₁ at hRel ⊢
  have hActNone : res₁.1.active = none := by
    dsimp only [releaseShamirShareFromVault] at hV1
    split at hV1
    · rw [← hV1] at hRel; cases hRel
    · split at hV1
      · rw [← hV1]
      · rw [← hV1] at hRel; cases hRel
  unfold releaseShamirShareFromVault
  split
  · rfl
  · have hNotSome : ¬(res₁.1.active = some r) := by rw [hActNone]; intro h; cases h
    simp only [hNotSome, ↓reduceIte]

/-- Certified `BeltLatch` mint check binding `BeltLatchRecord` to `Custody.Burn`:
    requires `b.intent.leaf < 2 ^ 64`, `rec.epoch = UInt64.ofNat b.intent.leaf`,
    `rec.msgDigest = H (intentCanonicalPayload b.intent)`, unpoisoned `nodeSt.inFlight = some rec`,
    and a valid `q`-of-`n` pairwise-MAC `BeltEcho` certificate `verifyQuorumEchoCertificate`. -/
def checkLatchCertifiedBurn {n : Nat}
    (H : List UInt8 → Digest256)
    (MAC : Digest256 → List UInt8 → Digest256)
    (macKeys : Fin n → Fin n → Digest256)
    (q : Nat) (verifier : Fin n) (nodeSt : BeltLatchNodeState)
    (Q : CustodiansMask n) (rec : BeltLatchRecord)
    (echoes : List (AuthenticatedBeltEcho n)) (b : Custody.Burn) : Bool :=
  !nodeSt.walPoisoned &&
  decide (nodeSt.inFlight = some rec) &&
  decide (b.intent.leaf < 2 ^ 64) &&
  decide (rec.epoch = UInt64.ofNat b.intent.leaf) &&
  decide (rec.msgDigest = H (intentCanonicalPayload b.intent)) &&
  verifyQuorumEchoCertificate H MAC macKeys q verifier Q rec echoes

/-- Per-custodian input alphabet for the `SimulationSpine.PartyMachine` refinement between
    concrete Shamir-custodian state and abstract `CompleteMediationBoundary` vault state. -/
inductive ShamirVaultMachineInput (n L : Nat) where
  | certifiedMint (anchor : Nat) (Q : CustodiansMask n) (rec : BeltLatchRecord)
      (echoes : List (AuthenticatedBeltEcho n)) (b : Custody.Burn)
  | releaseShare (anchor : Nat) (r : Custody.Intent) (counter : UInt32) (digits : Fin L → Fin 4)
  | forget
  | crash

/-- Per-custodian observable output event on `SimulationSpine`. -/
inductive ShamirVaultMachineOutput (n L : Nat) where
  | minted (intent : Custody.Intent)
  | shareReleased (opening : ShamirCustodianShareOpening n L)
  | wiped

/-- Concrete Shamir custodian state pairing local `BeltLatchNodeState` with `Custody.Vault`. -/
structure ShamirCustodianLocalState where
  latchNode : BeltLatchNodeState
  vault : Custody.Vault

/-- Step transition of the concrete Shamir custodian `PartyMachine`. -/
def shamirCustodianMachine {n L d : Nat}
    (H : List UInt8 → Digest256)
    (MAC : Digest256 → List UInt8 → Digest256)
    (macKeys : Fin n → Fin n → Digest256)
    (masterSeed : Digest256)
    (polyTape : UInt64 → PreSteppedDigest256ShamirTape d L)
    (evalPt : TowerElem 7) (party : Fin n)
    (q : Nat) (policy : Custody.RoundPolicy) (cap : Nat) :
    PartyMachine ShamirCustodianLocalState
      (ShamirVaultMachineInput n L) (ShamirVaultMachineOutput n L) :=
  PartyMachine.ofOutcome (fun s inp =>
    match inp with
    | .certifiedMint anchor Q rec echoes b =>
      if checkLatchCertifiedBurn H MAC macKeys q party s.latchNode Q rec echoes b then
        if s.vault.poisoned || decide (s.vault.durable.anchor ≠ anchor) then
          .err { s with vault := { s.vault with poisoned := true, active := none } } ()
        else if Custody.mintGuard policy cap s.vault b then
          let v' := Custody.mint policy cap anchor s.vault b
          .ok { s with vault := v' } (.minted b.intent)
        else
          .err s ()
      else
        .err s ()
    | .releaseShare anchor r counter digits =>
      let res := releaseShamirShareFromVault H masterSeed polyTape evalPt party anchor
        s.vault r counter digits
      match res.2 with
      | some op => .ok { s with vault := res.1 } (.shareReleased op)
      | none => .err { s with vault := res.1 } ()
    | .forget =>
      .ok { s with vault := Custody.forget s.vault } .wiped
    | .crash =>
      .ok { latchNode := beltLatchCrashAndRecover s.latchNode
            vault := Custody.forget s.vault } .wiped)

/-- Abstract `CompleteMediationBoundary` `PartyMachine` over `ShamirCustodianLocalState`'s
    projected `(latchNode, vault)` specification, delegating durable mediation directly to
    `Custody.mint`, `Custody.forget`, and one-time handle consumption. -/
def abstractMediationVaultMachine {n L d : Nat}
    (H : List UInt8 → Digest256)
    (MAC : Digest256 → List UInt8 → Digest256)
    (macKeys : Fin n → Fin n → Digest256)
    (masterSeed : Digest256)
    (polyTape : UInt64 → PreSteppedDigest256ShamirTape d L)
    (evalPt : TowerElem 7) (party : Fin n)
    (q : Nat) (policy : Custody.RoundPolicy) (cap : Nat) :
    PartyMachine (BeltLatchNodeState × Custody.Vault)
      (ShamirVaultMachineInput n L) (ShamirVaultMachineOutput n L) :=
  PartyMachine.ofOutcome (fun sv inp =>
    match inp with
    | .certifiedMint anchor Q rec echoes b =>
      if checkLatchCertifiedBurn H MAC macKeys q party sv.1 Q rec echoes b then
        if sv.2.poisoned || decide (sv.2.durable.anchor ≠ anchor) then
          .err (sv.1, Custody.mint policy cap anchor sv.2 b) ()
        else if Custody.mintGuard policy cap sv.2 b then
          .ok (sv.1, Custody.mint policy cap anchor sv.2 b) (.minted b.intent)
        else
          .err (sv.1, Custody.mint policy cap anchor sv.2 b) ()
      else
        .err sv ()
    | .releaseShare anchor r counter digits =>
      let res := releaseShamirShareFromVault H masterSeed polyTape evalPt party anchor
        sv.2 r counter digits
      match res.2 with
      | some op => .ok (sv.1, res.1) (.shareReleased op)
      | none => .err (sv.1, res.1) ()
    | .forget =>
      .ok (sv.1, Custody.forget sv.2) .wiped
    | .crash =>
      .ok (beltLatchCrashAndRecover sv.1, Custody.forget sv.2) .wiped)

/-- Exact `SimulationSpine.LockstepSim` from `shamirCustodianMachine` to
    `abstractMediationVaultMachine`, preserving `Custody.Safe policy cap s.vault` on every
    accepted and rejected transition (`0 Classical.choice`). -/
def shamirCustodianLockstepSim {n L d : Nat}
    (H : List UInt8 → Digest256)
    (MAC : Digest256 → List UInt8 → Digest256)
    (macKeys : Fin n → Fin n → Digest256)
    (masterSeed : Digest256)
    (polyTape : UInt64 → PreSteppedDigest256ShamirTape d L)
    (evalPt : TowerElem 7) (party : Fin n)
    (q : Nat) (policy : Custody.RoundPolicy) (cap : Nat) :
    LockstepSim
      (shamirCustodianMachine H MAC macKeys masterSeed polyTape evalPt party q policy cap)
      (abstractMediationVaultMachine H MAC macKeys masterSeed polyTape evalPt party q policy cap) where
  Inv s := Custody.Safe policy cap s.vault
  abs s := (s.latchNode, s.vault)
  step_eq {s} inp hInv := by
    cases inp with
    | certifiedMint anchor Q rec echoes b =>
      unfold shamirCustodianMachine abstractMediationVaultMachine PartyMachine.ofOutcome
      dsimp only
      by_cases hCert : checkLatchCertifiedBurn H MAC macKeys q party s.latchNode Q rec echoes b = true
      · simp only [hCert, ↓reduceIte]
        by_cases hPois : (s.vault.poisoned || decide (s.vault.durable.anchor ≠ anchor)) = true
        · simp only [hPois, ↓reduceIte]
          have hMintPois : Custody.mint policy cap anchor s.vault b =
              { s.vault with poisoned := true, active := none } := by
            unfold Custody.mint; simp only [hPois, ↓reduceIte]
          rw [hMintPois]
          exact ⟨hMintPois ▸ Custody.mint_safe policy cap anchor s.vault b hInv, trivial, rfl⟩
        · have hPoisF : (s.vault.poisoned || decide (s.vault.durable.anchor ≠ anchor)) = false :=
            Bool.not_eq_true _ |>.mp hPois
          simp only [hPoisF, Bool.false_eq_true, ↓reduceIte]
          by_cases hGuard : Custody.mintGuard policy cap s.vault b = true
          · simp only [hGuard, ↓reduceIte]
            exact ⟨Custody.mint_safe policy cap anchor s.vault b hInv, trivial⟩
          · have hGuardF : Custody.mintGuard policy cap s.vault b = false :=
              Bool.not_eq_true _ |>.mp hGuard
            simp only [hGuardF, Bool.false_eq_true, ↓reduceIte]
            have hMintNoop : Custody.mint policy cap anchor s.vault b = s.vault := by
              unfold Custody.mint
              simp only [hPoisF, hGuardF, Bool.false_eq_true, ↓reduceIte]
            rw [hMintNoop]
            exact ⟨hInv, trivial, rfl⟩
      · have hCertF : checkLatchCertifiedBurn H MAC macKeys q party s.latchNode Q rec echoes b = false :=
          Bool.not_eq_true _ |>.mp hCert
        simp only [hCertF, Bool.false_eq_true, ↓reduceIte]
        exact ⟨hInv, trivial, trivial⟩
    | releaseShare anchor r counter digits =>
      unfold shamirCustodianMachine abstractMediationVaultMachine PartyMachine.ofOutcome
      dsimp only
      have hRelSafe := releaseShamirShareFromVault_safe H masterSeed polyTape evalPt party
        policy cap anchor s.vault r counter digits hInv
      cases hOut : (releaseShamirShareFromVault H masterSeed polyTape evalPt party anchor
          s.vault r counter digits).2 with
      | some op =>
        dsimp only
        exact ⟨hRelSafe, rfl⟩
      | none =>
        dsimp only
        exact ⟨hRelSafe, rfl, rfl⟩
    | forget =>
      unfold shamirCustodianMachine abstractMediationVaultMachine PartyMachine.ofOutcome
      exact ⟨Custody.forget_safe policy cap s.vault hInv, rfl⟩
    | crash =>
      unfold shamirCustodianMachine abstractMediationVaultMachine PartyMachine.ofOutcome
      exact ⟨Custody.forget_safe policy cap s.vault hInv, rfl⟩

/-- Induced `SimulationSpine.ForwardSim` for each Shamir custodian (`0 Classical.choice`). -/
def shamirCustodianForwardSim {n L d : Nat}
    (H : List UInt8 → Digest256)
    (MAC : Digest256 → List UInt8 → Digest256)
    (macKeys : Fin n → Fin n → Digest256)
    (masterSeed : Digest256)
    (polyTape : UInt64 → PreSteppedDigest256ShamirTape d L)
    (evalPt : TowerElem 7) (party : Fin n)
    (q : Nat) (policy : Custody.RoundPolicy) (cap : Nat) :
    ForwardSim
      (shamirCustodianMachine H MAC macKeys masterSeed polyTape evalPt party q policy cap)
      (abstractMediationVaultMachine H MAC macKeys masterSeed polyTape evalPt party q policy cap) :=
  (shamirCustodianLockstepSim H MAC macKeys masterSeed polyTape evalPt party q policy cap).toForwardSim

/-! ## §3. Multi-Turn `(t, n)` Shamir + `2q > n + f` `BeltLatch` Network & Epoch Non-Equivocation -/

/-- Certified latch-mint provenance entry recorded when an honest custodian mints `intent` in its
    `Custody.Vault` after verifying a `q`-of-`n` `BeltLatch` echo certificate. -/
structure CertifiedVaultMintRecord (n : Nat) where
  quorum : CustodiansMask n
  latchRec : BeltLatchRecord
  echoes : List (AuthenticatedBeltEcho n)
  intent : Custody.Intent

/-- Online `(t, n)` Lagrange Shamir combiner producing a candidate `QuorumJortsSig` from
    `submitted : SubmittedDigest256ShamirShares L` and checking BOTH MAC-free WOTS+C endpoint
    self-verification (`preSteppedDigest256ReconstructAndSelfVerify`) AND full single-validator
    Merkle root verification (`verifyQuorumJortsSigAt`). -/
def combineAndVerifyShamirValidatorSig (L targetSum : Nat)
    (H : List UInt8 → Digest256) (validatorPk : QuorumPublicKey)
    (digitsOf : Digest256 → List (Fin 4))
    (lambdas : List (TowerElem 7))
    (r : Custody.Intent) (counter : UInt32)
    (submitted : SubmittedDigest256ShamirShares L)
    (authPath : List Digest256) : Option QuorumJortsSig :=
  let gLeaf := UInt64.ofNat r.leaf
  let msg := intentCanonicalPayload r
  let msgHash := quorumMessageHash H validatorPk gLeaf msg
  let dig := quorumCounterDigest H msgHash counter
  let digitsList := digitsOf dig
  if digitsList.length = L then
    let digitsFn : Fin L → Fin 4 := fun i => digitsList.getD i.1 ⟨0, by decide⟩
    let chainEndsFromPath := fun i : Fin L =>
      -- Reference chain endpoint check is performed by verifyQuorumJortsSigAt against validatorPk.root;
      -- here we reconstruct candidate nodes via Lagrange ringDot over GF(2^128)²:
      if (digitsFn i).val < 3 then
        joinTower128Digest256
          (ringDot lambdas (submitted i).1, ringDot lambdas (submitted i).2)
      else
        0#256
    let candNodes := (List.finRange L).map chainEndsFromPath
    let candSig : QuorumJortsSig :=
      { leaf := gLeaf, counter := counter, nodes := candNodes, authPath := authPath }
    if verifyQuorumJortsSigAt L targetSum H validatorPk digitsOf msg candSig then
      some candSig
    else
      none
  else
    none

/-- Full MAC-free self-verifying + Merkle-verifying `(t, n)` Shamir combiner when the leaf's
    public chain endpoints `leafChainPk : Fin L → Digest256` are also supplied (so chains with
    digit `d_i = 3` require `0` share transmissions!). -/
def combinePreSteppedShamirValidatorSig (L targetSum : Nat)
    (H : List UInt8 → Digest256) (validatorPk : QuorumPublicKey)
    (digitsOf : Digest256 → List (Fin 4))
    (leafChainPk : Fin L → Digest256)
    (lambdas : List (TowerElem 7))
    (r : Custody.Intent) (counter : UInt32)
    (submitted : SubmittedDigest256ShamirShares L)
    (authPath : List Digest256) : Option QuorumJortsSig :=
  let gLeaf := UInt64.ofNat r.leaf
  let msg := intentCanonicalPayload r
  let msgHash := quorumMessageHash H validatorPk gLeaf msg
  let dig := quorumCounterDigest H msgHash counter
  let digitsList := digitsOf dig
  let digitsFn : Fin L → Fin 4 := fun i => digitsList.getD i.1 ⟨0, by decide⟩
  match preSteppedDigest256ReconstructAndSelfVerify
      (quorumChainStep H validatorPk.pkSeed gLeaf) leafChainPk lambdas digitsFn submitted with
  | none => none
  | some candFn =>
    let candSig : QuorumJortsSig :=
      { leaf := gLeaf
        counter := counter
        nodes := (List.finRange L).map candFn
        authPath := authPath }
    if verifyQuorumJortsSigAt L targetSum H validatorPk digitsOf msg candSig then
      some candSig
    else
      none

/-- Distributed multi-turn `(t, n)` Shamir + `BeltLatch` custody network state. -/
structure ShamirCustodyNetworkState (n L : Nat) where
  beltTrace : List (BeltNetworkTurn n)
  beltNet : BeltLatchNetworkState n
  vaults : Fin n → Custody.Vault
  mintCerts : Fin n → List (CertifiedVaultMintRecord n)
  honestShareReleases : List (ShamirCustodianShareOpening n L)
  combinedSignatures : List (Custody.Intent × QuorumJortsSig)

/-- Initial `(t, n)` Shamir + `BeltLatch` custody network state at epoch `0`. -/
def ShamirCustodyNetworkState.init (n L height maxWindow : Nat) :
    ShamirCustodyNetworkState n L where
  beltTrace := []
  beltNet := BeltLatchNetworkState.init n height maxWindow
  vaults := fun _ => Custody.initial
  mintCerts := fun _ => []
  honestShareReleases := []
  combinedSignatures := []

/-- Open-world multi-turn schedule alphabet for `(t, n)` Shamir threshold custody. -/
inductive ShamirCustodyTurn (n L : Nat) where
  | belt (turn : BeltNetworkTurn n)
  | certifiedMint (p : Fin n) (anchor : Nat) (Q : CustodiansMask n)
      (rec : BeltLatchRecord) (echoes : List (AuthenticatedBeltEcho n)) (b : Custody.Burn)
  | releaseShare (p : Fin n) (anchor : Nat) (r : Custody.Intent) (counter : UInt32)
  | combineSig (leafChainPk : Fin L → Digest256) (lambdas : List (TowerElem 7))
      (r : Custody.Intent) (counter : UInt32)
      (submitted : SubmittedDigest256ShamirShares L) (authPath : List Digest256)
  | forgetVault (p : Fin n)
  | crashAndRecoverCustodian (p : Fin n)

/-- Static deployment parameters for a single-validator `(t, n)` Shamir custody cluster. -/
structure ShamirValidatorDeployment (n L d : Nat) where
  H : List UInt8 → Digest256
  MAC : Digest256 → List UInt8 → Digest256
  macKeys : Fin n → Fin n → Digest256
  Corrupt : CustodiansMask n
  t : Nat
  f : Nat
  q : Nat
  height : Nat
  maxWindow : Nat
  targetSum : Nat
  masterSeed : Digest256
  digitsOf : Digest256 → List (Fin 4)
  evalPts : Fin n → TowerElem 7
  polyTape : UInt64 → PreSteppedDigest256ShamirTape d L
  policies : Fin n → Custody.RoundPolicy
  caps : Fin n → Nat

/-- Derived single-validator `QuorumPublicKey` for deployment `dep`. -/
def ShamirValidatorDeployment.validatorPk {n L d : Nat}
    (dep : ShamirValidatorDeployment n L d) : QuorumPublicKey :=
  deriveQuorumValidatorPublicKey L dep.height dep.H dep.masterSeed

/-- Execute one open-world network transition on `ShamirCustodyNetworkState n L`. -/
def stepShamirCustody {n L d : Nat}
    (dep : ShamirValidatorDeployment n L d)
    (st : ShamirCustodyNetworkState n L)
    (turn : ShamirCustodyTurn n L) : ShamirCustodyNetworkState n L :=
  match turn with
  | .belt bTurn =>
    { st with
      beltTrace := st.beltTrace ++ [bTurn]
      beltNet := stepBeltNetwork dep.H dep.MAC dep.macKeys dep.Corrupt dep.q st.beltNet bTurn }
  | .certifiedMint p anchor Q rec echoes b =>
    if dep.Corrupt.mem p then st
    else if checkLatchCertifiedBurn dep.H dep.MAC dep.macKeys dep.q p
        (st.beltNet.nodes p) Q rec echoes b then
      let vOld := st.vaults p
      let vNew := Custody.mint (dep.policies p) (dep.caps p) anchor vOld b
      if !vOld.poisoned && decide (vOld.durable.anchor = anchor) &&
          Custody.mintGuard (dep.policies p) (dep.caps p) vOld b then
        { st with
          vaults := fun i => if i = p then vNew else st.vaults i
          mintCerts := fun i =>
            if i = p then ⟨Q, rec, echoes, b.intent⟩ :: st.mintCerts p else st.mintCerts i }
      else
        { st with vaults := fun i => if i = p then vNew else st.vaults i }
    else
      st
  | .releaseShare p anchor r counter =>
    if dep.Corrupt.mem p then st
    else
      let pk := dep.validatorPk
      let gLeaf := UInt64.ofNat r.leaf
      let msg := intentCanonicalPayload r
      let dig := quorumCounterDigest dep.H (quorumMessageHash dep.H pk gLeaf msg) counter
      let digitsList := dep.digitsOf dig
      let digitsFn : Fin L → Fin 4 := fun i => digitsList.getD i.1 ⟨0, by decide⟩
      let res := releaseShamirShareFromVault dep.H dep.masterSeed dep.polyTape
        (dep.evalPts p) p anchor (st.vaults p) r counter digitsFn
      match res.2 with
      | some op =>
        { st with
          vaults := fun i => if i = p then res.1 else st.vaults i
          honestShareReleases := op :: st.honestShareReleases }
      | none =>
        { st with vaults := fun i => if i = p then res.1 else st.vaults i }
  | .combineSig leafChainPk lambdas r counter submitted authPath =>
    match combinePreSteppedShamirValidatorSig L dep.targetSum dep.H dep.validatorPk
        dep.digitsOf leafChainPk lambdas r counter submitted authPath with
    | none => st
    | some sig => { st with combinedSignatures := (r, sig) :: st.combinedSignatures }
  | .forgetVault p =>
    if dep.Corrupt.mem p then st
    else
      { st with vaults := fun i => if i = p then Custody.forget (st.vaults p) else st.vaults i }
  | .crashAndRecoverCustodian p =>
    { st with
      beltTrace := st.beltTrace ++ [.crashAndRecoverNode p]
      beltNet := stepBeltNetwork dep.H dep.MAC dep.macKeys dep.Corrupt dep.q
        st.beltNet (.crashAndRecoverNode p)
      vaults := fun i =>
        if i = p && !dep.Corrupt.mem p then Custody.forget (st.vaults p) else st.vaults i }

/-- Execute a multi-turn open-world schedule `List (ShamirCustodyTurn n L)`. -/
def runShamirCustodyTrace {n L d : Nat}
    (dep : ShamirValidatorDeployment n L d)
    (st : ShamirCustodyNetworkState n L) :
    List (ShamirCustodyTurn n L) → ShamirCustodyNetworkState n L
  | [] => st
  | turn :: rest => runShamirCustodyTrace dep (stepShamirCustody dep st turn) rest

private theorem runBeltNetworkTrace_append {n : Nat}
    (H : List UInt8 → Digest256)
    (MAC : Digest256 → List UInt8 → Digest256)
    (macKeys : Fin n → Fin n → Digest256)
    (Corrupt : CustodiansMask n) (q : Nat)
    (initNet : BeltLatchNetworkState n)
    (tr : List (BeltNetworkTurn n)) (turn : BeltNetworkTurn n) :
    runBeltNetworkTrace H MAC macKeys Corrupt q initNet (tr ++ [turn]) =
      stepBeltNetwork H MAC macKeys Corrupt q
        (runBeltNetworkTrace H MAC macKeys Corrupt q initNet tr) turn := by
  induction tr generalizing initNet with
  | nil => rfl
  | cons t ts ih => exact ih _

/-- Joint multi-turn safety invariant across `BeltLatchNetworkState`, all `n` custodian
    `Custody.Vault`s, honest Shamir share releases, and combined validator signatures. -/
structure ShamirCustodyNetworkInv {n L d : Nat}
    (dep : ShamirValidatorDeployment n L d)
    (st : ShamirCustodyNetworkState n L) : Prop where
  beltSync :
    st.beltNet = runBeltNetworkTrace dep.H dep.MAC dep.macKeys dep.Corrupt dep.q
      (BeltLatchNetworkState.init n dep.height dep.maxWindow) st.beltTrace
  vaultSafe :
    ∀ p : Fin n, Custody.Safe (dep.policies p) (dep.caps p) (st.vaults p)
  burnedCertified :
    ∀ (p : Fin n), dep.Corrupt.mem p = false →
      ∀ b ∈ (st.vaults p).durable.burned,
        ∃ mc ∈ st.mintCerts p,
          mc.intent = b.intent ∧
          b.intent.leaf < 2 ^ 64 ∧
          mc.latchRec.epoch = UInt64.ofNat b.intent.leaf ∧
          mc.latchRec.msgDigest = dep.H (intentCanonicalPayload b.intent) ∧
          verifyQuorumEchoCertificate dep.H dep.MAC dep.macKeys dep.q p
            mc.quorum mc.latchRec mc.echoes = true
  shareReleaseProvenance :
    ∀ op ∈ st.honestShareReleases,
      dep.Corrupt.mem op.party = false ∧
      op.intent ∈ (st.vaults op.party).attempted ∧
      op.epoch = UInt64.ofNat op.intent.leaf
  shareReleasesNodupPartyIntent :
    (st.honestShareReleases.map (fun op => (op.party, op.intent))).Nodup
  combinedVerified :
    ∀ entry ∈ st.combinedSignatures,
      entry.2.leaf = UInt64.ofNat entry.1.leaf ∧
      verifyQuorumJortsSigAt L dep.targetSum dep.H dep.validatorPk dep.digitsOf
        (intentCanonicalPayload entry.1) entry.2 = true

theorem stepShamirCustody_preserves_inv {n L d : Nat}
    (dep : ShamirValidatorDeployment n L d)
    (st : ShamirCustodyNetworkState n L)
    (turn : ShamirCustodyTurn n L)
    (hInv : ShamirCustodyNetworkInv dep st) :
    ShamirCustodyNetworkInv dep (stepShamirCustody dep st turn) := by
  cases turn with
  | belt bTurn =>
    unfold stepShamirCustody
    refine ⟨?_, hInv.vaultSafe, hInv.burnedCertified, hInv.shareReleaseProvenance,
      hInv.shareReleasesNodupPartyIntent, hInv.combinedVerified⟩
    rw [runBeltNetworkTrace_append, ← hInv.beltSync]
  | certifiedMint p anchor Q rec echoes b =>
    unfold stepShamirCustody
    by_cases hCorr : dep.Corrupt.mem p = true
    · simp only [hCorr, ↓reduceIte]; exact hInv
    · have hHon : dep.Corrupt.mem p = false := Bool.not_eq_true _ |>.mp hCorr
      simp only [hHon, Bool.false_eq_true, ↓reduceIte]
      by_cases hLatch : checkLatchCertifiedBurn dep.H dep.MAC dep.macKeys dep.q p
          (st.beltNet.nodes p) Q rec echoes b = true
      · simp only [hLatch, ↓reduceIte]
        have hCertUnpack :
            b.intent.leaf < 2 ^ 64 ∧
            rec.epoch = UInt64.ofNat b.intent.leaf ∧
            rec.msgDigest = dep.H (intentCanonicalPayload b.intent) ∧
            verifyQuorumEchoCertificate dep.H dep.MAC dep.macKeys dep.q p Q rec echoes = true := by
          unfold checkLatchCertifiedBurn at hLatch
          rcases Bool.and_eq_true_iff.mp hLatch with ⟨h15, hVerQ⟩
          rcases Bool.and_eq_true_iff.mp h15 with ⟨h14, hMd⟩
          rcases Bool.and_eq_true_iff.mp h14 with ⟨h13, hEp⟩
          rcases Bool.and_eq_true_iff.mp h13 with ⟨_, hLf⟩
          exact ⟨of_decide_eq_true hLf, of_decide_eq_true hEp, of_decide_eq_true hMd, hVerQ⟩
        by_cases hGrant : (!((st.vaults p).poisoned) &&
            decide ((st.vaults p).durable.anchor = anchor) &&
            Custody.mintGuard (dep.policies p) (dep.caps p) (st.vaults p) b) = true
        · simp only [hGrant, ↓reduceIte]
          refine ⟨hInv.beltSync, ?_, ?_, ?_, hInv.shareReleasesNodupPartyIntent,
            hInv.combinedVerified⟩
          · intro i
            by_cases hip : i = p
            · subst hip; simp only [↓reduceIte]
              exact Custody.mint_safe _ _ anchor _ b (hInv.vaultSafe i)
            · simp only [hip, ↓reduceIte]; exact hInv.vaultSafe i
          · intro i hiHon b' hb'
            by_cases hip : i = p
            · subst hip
              simp only [↓reduceIte] at hb' ⊢
              have hMintEq : (Custody.mint (dep.policies i) (dep.caps i) anchor (st.vaults i) b).durable.burned =
                  b :: (st.vaults i).durable.burned := by
                rcases Bool.and_eq_true_iff.mp hGrant with ⟨hPA, hMG⟩
                rcases Bool.and_eq_true_iff.mp hPA with ⟨hNP, hAnc⟩
                have hPF : (st.vaults i).poisoned = false := Bool.not_eq_true _ |>.mp
                  (fun hT => by rw [hT] at hNP; cases hNP)
                have hAEq : (st.vaults i).durable.anchor = anchor := of_decide_eq_true hAnc
                unfold Custody.mint
                simp [hPF, hAEq, hMG]
              rw [hMintEq] at hb'
              rcases List.mem_cons.mp hb' with rfl | hOldB
              · exact ⟨⟨Q, rec, echoes, b'.intent⟩, .head _, rfl,
                  hCertUnpack.1, hCertUnpack.2.1, hCertUnpack.2.2.1, hCertUnpack.2.2.2⟩
              · obtain ⟨mc, hmc, h1, h2, h3, h4, h5⟩ := hInv.burnedCertified i hiHon b' hOldB
                exact ⟨mc, .tail _ hmc, h1, h2, h3, h4, h5⟩
            · simp only [hip, ↓reduceIte] at hb' ⊢
              exact hInv.burnedCertified i hiHon b' hb'
          · intro op hop
            obtain ⟨hOpHon, hAtt, hEp⟩ := hInv.shareReleaseProvenance op hop
            refine ⟨hOpHon, ?_, hEp⟩
            by_cases hopp : op.party = p
            · rw [hopp] at hAtt ⊢
              simp only [↓reduceIte]
              unfold Custody.mint
              split
              · exact hAtt
              · split <;> exact hAtt
            · simp only [hopp, ↓reduceIte]; exact hAtt
        · have hGrantF : (!((st.vaults p).poisoned) &&
              decide ((st.vaults p).durable.anchor = anchor) &&
              Custody.mintGuard (dep.policies p) (dep.caps p) (st.vaults p) b) = false :=
            Bool.not_eq_true _ |>.mp hGrant
          simp only [hGrantF, Bool.false_eq_true, ↓reduceIte]
          have hBurnUnchanged :
              (Custody.mint (dep.policies p) (dep.caps p) anchor (st.vaults p) b).durable.burned =
              (st.vaults p).durable.burned := by
            unfold Custody.mint
            split
            · rfl
            · rename_i hNotPoisOrAnc
              split
              · rename_i hMG
                exfalso
                have hPF : (st.vaults p).poisoned = false := by
                  cases hP : (st.vaults p).poisoned
                  · rfl
                  · simp [hP] at hNotPoisOrAnc
                have hAEq : (st.vaults p).durable.anchor = anchor := by
                  by_cases hA : (st.vaults p).durable.anchor = anchor
                  · exact hA
                  · simp [hPF, hA] at hNotPoisOrAnc
                have hGTrue : (!((st.vaults p).poisoned) &&
                    decide ((st.vaults p).durable.anchor = anchor) &&
                    Custody.mintGuard (dep.policies p) (dep.caps p) (st.vaults p) b) = true := by
                  simp [hPF, hAEq, hMG]
                rw [hGTrue] at hGrantF
                cases hGrantF
              · rfl
          refine ⟨hInv.beltSync, ?_, ?_, ?_, hInv.shareReleasesNodupPartyIntent,
            hInv.combinedVerified⟩
          · intro i
            by_cases hip : i = p
            · subst hip; simp only [↓reduceIte]
              exact Custody.mint_safe _ _ anchor _ b (hInv.vaultSafe i)
            · simp only [hip, ↓reduceIte]; exact hInv.vaultSafe i
          · intro i hiHon b' hb'
            by_cases hip : i = p
            · subst hip
              simp only [↓reduceIte, hBurnUnchanged] at hb'
              exact hInv.burnedCertified i hiHon b' hb'
            · simp only [hip, ↓reduceIte] at hb'
              exact hInv.burnedCertified i hiHon b' hb'
          · intro op hop
            obtain ⟨hOpHon, hAtt, hEp⟩ := hInv.shareReleaseProvenance op hop
            refine ⟨hOpHon, ?_, hEp⟩
            by_cases hopp : op.party = p
            · rw [hopp] at hAtt ⊢
              simp only [↓reduceIte]
              unfold Custody.mint
              split
              · exact hAtt
              · split <;> exact hAtt
            · simp only [hopp, ↓reduceIte]; exact hAtt
      · have hLatchF : checkLatchCertifiedBurn dep.H dep.MAC dep.macKeys dep.q p
            (st.beltNet.nodes p) Q rec echoes b = false := Bool.not_eq_true _ |>.mp hLatch
        simp only [hLatchF, Bool.false_eq_true, ↓reduceIte]
        exact hInv
  | releaseShare p anchor r counter =>
    unfold stepShamirCustody
    by_cases hCorr : dep.Corrupt.mem p = true
    · simp only [hCorr, ↓reduceIte]; exact hInv
    · have hHon : dep.Corrupt.mem p = false := Bool.not_eq_true _ |>.mp hCorr
      simp only [hHon, Bool.false_eq_true, ↓reduceIte]
      let pk := dep.validatorPk
      let gLeaf := UInt64.ofNat r.leaf
      let msg := intentCanonicalPayload r
      let dig := quorumCounterDigest dep.H (quorumMessageHash dep.H pk gLeaf msg) counter
      let digitsList := dep.digitsOf dig
      let digitsFn : Fin L → Fin 4 := fun i => digitsList.getD i.1 ⟨0, by decide⟩
      let res := releaseShamirShareFromVault dep.H dep.masterSeed dep.polyTape
        (dep.evalPts p) p anchor (st.vaults p) r counter digitsFn
      have hResSafe : Custody.Safe (dep.policies p) (dep.caps p) res.1 :=
        releaseShamirShareFromVault_safe dep.H dep.masterSeed dep.polyTape (dep.evalPts p) p
          (dep.policies p) (dep.caps p) anchor (st.vaults p) r counter digitsFn (hInv.vaultSafe p)
      have hResBurn : res.1.durable.burned = (st.vaults p).durable.burned := by
        dsimp only [res, releaseShamirShareFromVault]
        split
        · rfl
        · split <;> rfl
      cases hOut : res.2 with
      | some op =>
        dsimp only
        have hRelUnpack :
            (st.vaults p).active = some r ∧
            res.1.attempted = r :: (st.vaults p).attempted ∧
            op.party = p ∧ op.intent = r ∧ op.epoch = UInt64.ofNat r.leaf := by
          dsimp only [res, releaseShamirShareFromVault] at hOut ⊢
          split at hOut
          · cases hOut
          · split at hOut
            · rename_i hNP hAct
              have hNPF : ((st.vaults p).poisoned || decide ((st.vaults p).durable.anchor ≠ anchor)) = false :=
                Bool.not_eq_true _ |>.mp hNP
              injection hOut with hOpEq
              rw [← hOpEq]
              simp only [hNPF, Bool.false_eq_true, ↓reduceIte, hAct, computeShamirCustodianOpening,
                and_self]
            · cases hOut
        refine ⟨hInv.beltSync, ?_, ?_, ?_, ?_, hInv.combinedVerified⟩
        · intro i
          by_cases hip : i = p
          · subst hip; simp only [↓reduceIte]; exact hResSafe
          · simp only [hip, ↓reduceIte]; exact hInv.vaultSafe i
        · intro i hiHon b' hb'
          by_cases hip : i = p
          · subst hip; simp only [↓reduceIte] at hb'; rw [hResBurn] at hb'
            exact hInv.burnedCertified i hiHon b' hb'
          · simp only [hip, ↓reduceIte] at hb'
            exact hInv.burnedCertified i hiHon b' hb'
        · intro op' hop'
          rcases List.mem_cons.mp hop' with rfl | hOldOp
          · refine ⟨hRelUnpack.2.2.1 ▸ hHon, ?_, hRelUnpack.2.2.2.1.symm ▸ hRelUnpack.2.2.2.2⟩
            rw [hRelUnpack.2.2.1, hRelUnpack.2.2.2.1]
            simp only [↓reduceIte]
            rw [hRelUnpack.2.1]
            exact .head _
          · obtain ⟨hOpHon, hAtt, hEp⟩ := hInv.shareReleaseProvenance op' hOldOp
            refine ⟨hOpHon, ?_, hEp⟩
            by_cases hopp : op'.party = p
            · rw [hopp] at hAtt ⊢
              simp only [↓reduceIte]
              rw [hRelUnpack.2.1]
              exact .tail _ hAtt
            · simp only [hopp, ↓reduceIte]; exact hAtt
        · simp only [List.map_cons, List.nodup_cons]
          refine ⟨?_, hInv.shareReleasesNodupPartyIntent⟩
          intro hMemMap
          obtain ⟨opOld, hOldMem, hPairEq⟩ := List.mem_map.mp hMemMap
          rcases Prod.mk.inj hPairEq with ⟨hPartyOld, hIntentOld⟩
          obtain ⟨_, hAttOld, _⟩ := hInv.shareReleaseProvenance opOld hOldMem
          rw [hPartyOld, hRelUnpack.2.2.1, hIntentOld, hRelUnpack.2.2.2.1] at hAttOld
          exact (hInv.vaultSafe p).activeFresh r hRelUnpack.1 hAttOld
      | none =>
        dsimp only
        have hAttSub : ∀ s ∈ (st.vaults p).attempted, s ∈ res.1.attempted := by
          intro s hs
          dsimp only [res, releaseShamirShareFromVault]
          split
          · exact hs
          · split
            · exact .tail _ hs
            · exact hs
        refine ⟨hInv.beltSync, ?_, ?_, ?_, hInv.shareReleasesNodupPartyIntent,
          hInv.combinedVerified⟩
        · intro i
          by_cases hip : i = p
          · subst hip; simp only [↓reduceIte]; exact hResSafe
          · simp only [hip, ↓reduceIte]; exact hInv.vaultSafe i
        · intro i hiHon b' hb'
          by_cases hip : i = p
          · subst hip; simp only [↓reduceIte] at hb'; rw [hResBurn] at hb'
            exact hInv.burnedCertified i hiHon b' hb'
          · simp only [hip, ↓reduceIte] at hb'
            exact hInv.burnedCertified i hiHon b' hb'
        · intro op' hop'
          obtain ⟨hOpHon, hAtt, hEp⟩ := hInv.shareReleaseProvenance op' hop'
          refine ⟨hOpHon, ?_, hEp⟩
          by_cases hopp : op'.party = p
          · rw [hopp] at hAtt ⊢
            simp only [↓reduceIte]
            exact hAttSub _ hAtt
          · simp only [hopp, ↓reduceIte]; exact hAtt
  | combineSig leafChainPk lambdas r counter submitted authPath =>
    unfold stepShamirCustody
    dsimp only
    cases hComb : combinePreSteppedShamirValidatorSig L dep.targetSum dep.H dep.validatorPk
        dep.digitsOf leafChainPk lambdas r counter submitted authPath with
    | none => exact hInv
    | some sig =>
      dsimp only
      have hCombOk :
          sig.leaf = UInt64.ofNat r.leaf ∧
          verifyQuorumJortsSigAt L dep.targetSum dep.H dep.validatorPk dep.digitsOf
            (intentCanonicalPayload r) sig = true := by
        unfold combinePreSteppedShamirValidatorSig at hComb
        dsimp only at hComb
        split at hComb
        · cases hComb
        · split at hComb
          · rename_i candFn _ hVer
            injection hComb with hSigEq
            rw [← hSigEq]
            exact ⟨rfl, hVer⟩
          · cases hComb
      refine ⟨hInv.beltSync, hInv.vaultSafe, hInv.burnedCertified,
        hInv.shareReleaseProvenance, hInv.shareReleasesNodupPartyIntent, ?_⟩
      intro entry hMem
      rcases List.mem_cons.mp hMem with rfl | hOld
      · exact hCombOk
      · exact hInv.combinedVerified entry hOld
  | forgetVault p =>
    unfold stepShamirCustody
    dsimp only
    by_cases hCorr : dep.Corrupt.mem p = true
    · simp only [hCorr, ↓reduceIte]; exact hInv
    · have hHon : dep.Corrupt.mem p = false := Bool.not_eq_true _ |>.mp hCorr
      simp only [hHon, Bool.false_eq_true, ↓reduceIte]
      refine ⟨hInv.beltSync, ?_, ?_, ?_, hInv.shareReleasesNodupPartyIntent,
        hInv.combinedVerified⟩
      · intro i
        by_cases hip : i = p
        · subst hip; simp only [↓reduceIte]
          exact Custody.forget_safe _ _ _ (hInv.vaultSafe i)
        · simp only [hip, ↓reduceIte]; exact hInv.vaultSafe i
      · intro i hiHon b' hb'
        by_cases hip : i = p
        · subst hip; simp only [↓reduceIte, Custody.forget] at hb'
          exact hInv.burnedCertified i hiHon b' hb'
        · simp only [hip, ↓reduceIte] at hb'
          exact hInv.burnedCertified i hiHon b' hb'
      · intro op hop
        obtain ⟨hOpHon, hAtt, hEp⟩ := hInv.shareReleaseProvenance op hop
        refine ⟨hOpHon, ?_, hEp⟩
        by_cases hopp : op.party = p
        · rw [hopp] at hAtt ⊢; simp [Custody.forget, hAtt]
        · simp [hopp, hAtt]
  | crashAndRecoverCustodian p =>
    unfold stepShamirCustody
    dsimp only
    refine ⟨?_, ?_, ?_, ?_, hInv.shareReleasesNodupPartyIntent, hInv.combinedVerified⟩
    · rw [runBeltNetworkTrace_append, ← hInv.beltSync]
    · intro i
      dsimp only
      by_cases hip : i = p
      · subst hip
        cases hC : dep.Corrupt.mem i
        · simp only [Bool.not_false]
          exact Custody.forget_safe _ _ _ (hInv.vaultSafe i)
        · simp only [Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
          exact hInv.vaultSafe i
      · have hDecF : decide (i = p) = false := decide_eq_false hip
        simp only [hDecF, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
        exact hInv.vaultSafe i
    · intro i hiHon b' hb'
      dsimp only at hb'
      by_cases hip : i = p
      · subst hip
        simp only [hiHon, Bool.not_false, Custody.forget] at hb'
        exact hInv.burnedCertified i hiHon b' hb'
      · have hDecF : decide (i = p) = false := decide_eq_false hip
        simp only [hDecF, Bool.false_and, Bool.false_eq_true, ↓reduceIte] at hb'
        exact hInv.burnedCertified i hiHon b' hb'
    · intro op hop
      obtain ⟨hOpHon, hAtt, hEp⟩ := hInv.shareReleaseProvenance op hop
      dsimp only
      refine ⟨hOpHon, ?_, hEp⟩
      by_cases hopp : op.party = p
      · rw [hopp] at hOpHon hAtt ⊢
        simp only [hOpHon, Bool.not_false, Custody.forget]
        exact hAtt
      · have hDecF : decide (op.party = p) = false := decide_eq_false hopp
        simp only [hDecF, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
        exact hAtt

theorem runShamirCustodyTrace_inv {n L d : Nat}
    (dep : ShamirValidatorDeployment n L d)
    (trace : List (ShamirCustodyTurn n L)) :
    ShamirCustodyNetworkInv dep
      (runShamirCustodyTrace dep
        (ShamirCustodyNetworkState.init n L dep.height dep.maxWindow) trace) := by
  have hInit : ShamirCustodyNetworkInv dep
      (ShamirCustodyNetworkState.init n L dep.height dep.maxWindow) :=
    { beltSync := rfl
      vaultSafe := fun p => Custody.initial_safe (dep.policies p) (dep.caps p)
      burnedCertified := fun _ _ _ h => by cases h
      shareReleaseProvenance := fun _ h => by cases h
      shareReleasesNodupPartyIntent := List.nodup_nil
      combinedVerified := fun _ h => by cases h }
  generalize ShamirCustodyNetworkState.init n L dep.height dep.maxWindow = st₀ at hInit
  induction trace generalizing st₀ with
  | nil => exact hInit
  | cons turn rest ih =>
    exact ih _ (stepShamirCustody_preserves_inv dep st₀ turn hInit)

/-- Predicate stating that every honest member of `t`-quorum `S` (`S.mem p = true`,
    `Corrupt.mem p = false`) released its Shamir share for `intent` during `st`. -/
def HonestQuorumReleasedIntent {n L : Nat}
    (Corrupt : CustodiansMask n) (st : ShamirCustodyNetworkState n L)
    (S : CustodiansMask n) (intent : Custody.Intent) : Prop :=
  ∀ p : Fin n, S.mem p = true → Corrupt.mem p = false →
    ∃ op ∈ st.honestShareReleases, op.party = p ∧ op.intent = intent

/-- **Crown Jewel 1 (`M3` Epoch Non-Equivocation) — `(t, n)` Shamir + `2q > n + f` `BeltLatch`
    Multi-Turn Non-Equivocation (`shamir_custody_epoch_non_equivocation`)**:
    Under `maskCard dep.Corrupt ≤ dep.f`, `dep.f < dep.t`, and `2 * dep.q > n + dep.f`, across ANY
    reachable multi-turn state `st = runShamirCustodyTrace dep init trace`:
    1. **Per-Custodian Unconditional Leaf Uniqueness & Spend Cap:** Every custodian's `Custody.Vault`
       satisfies `(st.vaults p).durable.spent ≤ dep.caps p`, and no honest custodian ever releases
       Shamir shares for two distinct intents `r₁ ≠ r₂` at the same leaf epoch `r₁.leaf = r₂.leaf`.
    2. **Global `(q, t)` Epoch Non-Equivocation:** Whenever two `t`-subsets `S₁, S₂`
       (`dep.t ≤ maskCard S₁`, `dep.t ≤ maskCard S₂`) obtain Shamir share releases from their
       honest members for intents `r₁` and `r₂` at the **same leaf epoch** (`r₁.leaf = r₂.leaf`),
       we constructively extract honest share-holders `h₁ ∈ S₁ \ Corrupt` and `h₂ ∈ S₂ \ Corrupt`
       plus an honest latch witness `pLatch ∈ (Q₁ ∩ Q₂) \ Corrupt`, and prove that EITHER:
       - `r₁ = r₂` (exact message/session/round/spend agreement — zero equivocation!), OR
       - an explicit `PairwiseEchoMacForgery` on `st.beltNet.emittedHonestEchoes` occurred, OR
       - an explicit 256-bit `HashCollision256 dep.H` (`intentCanonicalPayload r₁ ≠ intentCanonicalPayload r₂`
         with equal `dep.H` digests) occurred! -/
theorem shamir_custody_epoch_non_equivocation {n L d : Nat}
    (dep : ShamirValidatorDeployment n L d)
    (hCorrupt : maskCard dep.Corrupt ≤ dep.f)
    (hFltT : dep.f < dep.t)
    (hLatchQuorum : 2 * dep.q > n + dep.f)
    (trace : List (ShamirCustodyTurn n L)) :
    let st := runShamirCustodyTrace dep
      (ShamirCustodyNetworkState.init n L dep.height dep.maxWindow) trace
    -- (1) Spend cap & unconditional per-honest-custodian leaf uniqueness:
    (∀ p : Fin n, (st.vaults p).durable.spent ≤ dep.caps p) ∧
    (∀ op₁ ∈ st.honestShareReleases, ∀ op₂ ∈ st.honestShareReleases,
      op₁.party = op₂.party → op₁.intent.leaf = op₂.intent.leaf → op₁.intent = op₂.intent) ∧
    -- (2) Global cross-quorum (q, t) epoch non-equivocation:
    (∀ (S₁ S₂ : CustodiansMask n) (r₁ r₂ : Custody.Intent),
      dep.t ≤ maskCard S₁ →
      dep.t ≤ maskCard S₂ →
      HonestQuorumReleasedIntent dep.Corrupt st S₁ r₁ →
      HonestQuorumReleasedIntent dep.Corrupt st S₂ r₂ →
      r₁.leaf = r₂.leaf →
      r₁ = r₂ ∨
        Nonempty (PairwiseEchoMacForgery dep.MAC dep.macKeys dep.Corrupt
          st.beltNet.emittedHonestEchoes) ∨
        Nonempty (HashCollision256 dep.H)) := by
  intro st
  have hInv := runShamirCustodyTrace_inv dep trace
  refine ⟨fun p => (hInv.vaultSafe p).budget, ?_, ?_⟩
  · -- Part 1b: Per-honest-custodian leaf uniqueness
    intro op₁ hMem₁ op₂ hMem₂ hSameParty hSameLeaf
    obtain ⟨_, hAtt₁, _⟩ := hInv.shareReleaseProvenance op₁ hMem₁
    obtain ⟨_, hAtt₂, _⟩ := hInv.shareReleaseProvenance op₂ hMem₂
    rw [← hSameParty] at hAtt₂
    have hSafe := hInv.vaultSafe op₁.party
    obtain ⟨b₁, hb₁, hb₁Eq⟩ := hSafe.attemptedBurned op₁.intent hAtt₁
    obtain ⟨b₂, hb₂, hb₂Eq⟩ := hSafe.attemptedBurned op₂.intent hAtt₂
    rw [← hb₁Eq, ← hb₂Eq]
    exact hSafe.uniqueLeaf b₁ hb₁ b₂ hb₂ (by rw [hb₁Eq, hb₂Eq]; exact hSameLeaf)
  · -- Part 2: Global (q, t) epoch non-equivocation across S₁ and S₂
    intro S₁ S₂ r₁ r₂ hCard₁ hCard₂ hRel₁ hRel₂ hSameLeaf
    have hDiff₁ : 0 < maskCard (maskDiff S₁ dep.Corrupt) := by
      have hGe := maskCard_diff_ge S₁ dep.Corrupt; omega
    have hDiff₂ : 0 < maskCard (maskDiff S₂ dep.Corrupt) := by
      have hGe := maskCard_diff_ge S₂ dep.Corrupt; omega
    let ⟨h₁, hh₁⟩ := extractMaskMember (maskDiff S₁ dep.Corrupt) hDiff₁
    let ⟨h₂, hh₂⟩ := extractMaskMember (maskDiff S₂ dep.Corrupt) hDiff₂
    simp only [maskDiff, Bool.and_eq_true, Bool.not_eq_true'] at hh₁ hh₂
    obtain ⟨op₁, hop₁, hp₁Eq, hr₁Eq⟩ := hRel₁ h₁ hh₁.1 hh₁.2
    obtain ⟨op₂, hop₂, hp₂Eq, hr₂Eq⟩ := hRel₂ h₂ hh₂.1 hh₂.2
    obtain ⟨_, hAtt₁, _⟩ := hInv.shareReleaseProvenance op₁ hop₁
    obtain ⟨_, hAtt₂, _⟩ := hInv.shareReleaseProvenance op₂ hop₂
    rw [hp₁Eq, hr₁Eq] at hAtt₁
    rw [hp₂Eq, hr₂Eq] at hAtt₂
    obtain ⟨b₁, hb₁, hbi₁⟩ := (hInv.vaultSafe h₁).attemptedBurned r₁ hAtt₁
    obtain ⟨b₂, hb₂, hbi₂⟩ := (hInv.vaultSafe h₂).attemptedBurned r₂ hAtt₂
    obtain ⟨mc₁, _, hmcInt₁, _, hEp₁, hMd₁, hCert₁⟩ := hInv.burnedCertified h₁ hh₁.2 b₁ hb₁
    obtain ⟨mc₂, _, hmcInt₂, _, hEp₂, hMd₂, hCert₂⟩ := hInv.burnedCertified h₂ hh₂.2 b₂ hb₂
    have hQ₁ : dep.q ≤ maskCard mc₁.quorum :=
      of_decide_eq_true (Bool.and_eq_true_iff.mp hCert₁).1
    have hQ₂ : dep.q ≤ maskCard mc₂.quorum :=
      of_decide_eq_true (Bool.and_eq_true_iff.mp hCert₂).1
    have hSameRecEpoch : mc₁.latchRec.epoch = mc₂.latchRec.epoch := by
      rw [hEp₁, hEp₂, hbi₁, hbi₂, hSameLeaf]
    have hBeltUniq := beltLatch_quorum_intersection_global_uniqueness
      (height := dep.height) (maxWindow := dep.maxWindow)
      dep.H dep.MAC dep.macKeys dep.Corrupt mc₁.quorum mc₂.quorum
      hLatchQuorum hCorrupt hQ₁ hQ₂ st.beltTrace h₁ h₂ hh₁.2 hh₂.2
      mc₁.latchRec mc₂.latchRec hSameRecEpoch mc₁.echoes mc₂.echoes hCert₁ hCert₂
    rw [← hInv.beltSync] at hBeltUniq
    rcases hBeltUniq.2.2 with ⟨_, hMsgDigEq, _, _⟩ | hMacForge
    · by_cases hEqR : r₁ = r₂
      · exact .inl hEqR
      · right; right
        have hPayNe : intentCanonicalPayload r₁ ≠ intentCanonicalPayload r₂ :=
          fun hPayEq => hEqR (intentCanonicalPayload_injective hPayEq)
        have hHashEq : dep.H (intentCanonicalPayload r₁) = dep.H (intentCanonicalPayload r₂) := by
          rw [← hbi₁, ← hMd₁, hMsgDigEq, hMd₂, hbi₂]
        exact ⟨⟨intentCanonicalPayload r₁, intentCanonicalPayload r₂, hPayNe, hHashEq⟩⟩
    · exact .inr (.inl hMacForge)

/-! ## §4. Single-Validator Lagrange `(t, n)` Signature Reconstruction & Hypertree Bridge -/

/-- Assemble `SubmittedDigest256ShamirShares L` from `t` honest custodian share openings. -/
def assembleSubmittedSharesFromOpenings {n L : Nat}
    (openings : List (ShamirCustodianShareOpening n L)) :
    SubmittedDigest256ShamirShares L :=
  fun i =>
    (openings.filterMap (fun op => (op.chainShares i).map Prod.fst),
     openings.filterMap (fun op => (op.chainShares i).map Prod.snd))

/-- **Crown Jewel 2A (`M3` Single-Validator Reconstruction & Collision Soundness) —
    (`shamir_custody_combined_sig_verifies_or_collision`)**:
    For the single enrolled validator public key `validatorPk = dep.validatorPk`
    (`dep.height < 256`, `32 * L < 256 ^ 8`):
    1. **Honest `(t, n)` Completeness & Single-Key Verification:** Whenever `t` custodians at
       evaluation points `pts` with Lagrange weights `lambdas` (`∀ c₀ tail, ringDot lambdas ... = c₀`)
       release honest `ShamirCustodianShareOpening`s for `(r, counter)` (`r.leaf < 2 ^ dep.height`,
       `counter.toNat < 2 ^ 16`, balanced digits of length `L`), `combinePreSteppedShamirValidatorSig`
       deterministically outputs `some (quorumJortsReferenceSign ...)` AND that signature verifies
       under the single enrolled `validatorPk`!
    2. **Quorum Invariance (`QS-B`):** Any two honest `t`-subsets `(parties₁, lambdas₁)` and
       `(parties₂, lambdas₂)` reconstruct the **bit-for-bit identical** single-validator
       `QuorumJortsSig`!
    3. **Concrete `(t = 2, n = 4)` `GF(2^128)` (`TowerElem 7`) Instantiation:** Any two distinct
       custodian points `x₀ ≠ x₁` in `TowerElem 7` satisfy the Lagrange hypothesis via
       `lagrange2WeightsTower 7 x₀ x₁`.
    4. **Adversarial Share-Corruption & Combiner Soundness:** Every `(r, sig)` recorded in
       `st.combinedSignatures` along any multi-turn trace verifies under `validatorPk`, AND
       constructively either equals the exact single-validator reference chain nodes or yields an
       explicit `WotsChainCollisionWitness` / `HashCollision256 dep.H`! -/
theorem shamir_custody_combined_sig_verifies_or_collision {n L d : Nat}
    (dep : ShamirValidatorDeployment n L d)
    (hHeightLt : dep.height < 256)
    (hChainBound : 32 * L < 256 ^ 8) :
    let pk := dep.validatorPk
    -- (1) Honest (t, n) completeness & verification under single enrolled validatorPk:
    (∀ (parties : List (Fin n)) (lambdas : List (TowerElem 7))
       (r : Custody.Intent) (counter : UInt32),
      let gLeaf := UInt64.ofNat r.leaf
      let msg := intentCanonicalPayload r
      let digits := dep.digitsOf (quorumCounterDigest dep.H (quorumMessageHash dep.H pk gLeaf msg) counter)
      let digitsFn : Fin L → Fin 4 := fun i => digits.getD i.1 ⟨0, by decide⟩
      let leafChainPk : Fin L → Digest256 := fun i =>
        wotsChainIter (quorumChainStep dep.H pk.pkSeed gLeaf) i.1 0 3
          (quorumStageChainSk dep.H dep.masterSeed gLeaf (UInt32.ofNat i.1))
      let authPath := quorumAuthPath dep.H pk.pkSeed
        (quorumHonestLeafDigest L dep.H dep.masterSeed) dep.height 0 gLeaf.toNat
      let openings := parties.map (fun p =>
        computeShamirCustodianOpening dep.H dep.masterSeed dep.polyTape (dep.evalPts p)
          p r counter digitsFn)
      (∀ (c₀ : TowerElem 7) (tail : ShamirPadPoly (TowerElem 7) d),
        ringDot lambdas ((parties.map dep.evalPts).map
          (fun x => RoundPoly.evalCoeffs (c₀ :: tail.1) x)) = c₀) →
      r.leaf < 2 ^ dep.height →
      r.leaf < 2 ^ 64 →
      counter.toNat < 2 ^ 16 →
      digits.length = L →
      ((digits.map Fin.val).foldr (· + ·) 0) = dep.targetSum →
      combinePreSteppedShamirValidatorSig L dep.targetSum dep.H pk dep.digitsOf
        leafChainPk lambdas r counter (assembleSubmittedSharesFromOpenings openings) authPath =
          some (quorumJortsReferenceSign dep.H dep.masterSeed gLeaf counter digits authPath) ∧
      verifyQuorumJortsSigAt L dep.targetSum dep.H pk dep.digitsOf msg
        (quorumJortsReferenceSign dep.H dep.masterSeed gLeaf counter digits authPath) = true) ∧
    -- (2) Quorum invariance across any two honest t-subsets:
    (∀ (parties₁ parties₂ : List (Fin n)) (lambdas₁ lambdas₂ : List (TowerElem 7))
       (r : Custody.Intent) (counter : UInt32),
      let gLeaf := UInt64.ofNat r.leaf
      let msg := intentCanonicalPayload r
      let digits := dep.digitsOf (quorumCounterDigest dep.H (quorumMessageHash dep.H pk gLeaf msg) counter)
      let digitsFn : Fin L → Fin 4 := fun i => digits.getD i.1 ⟨0, by decide⟩
      let leafChainPk : Fin L → Digest256 := fun i =>
        wotsChainIter (quorumChainStep dep.H pk.pkSeed gLeaf) i.1 0 3
          (quorumStageChainSk dep.H dep.masterSeed gLeaf (UInt32.ofNat i.1))
      let authPath := quorumAuthPath dep.H pk.pkSeed
        (quorumHonestLeafDigest L dep.H dep.masterSeed) dep.height 0 gLeaf.toNat
      let ops₁ := parties₁.map (fun p =>
        computeShamirCustodianOpening dep.H dep.masterSeed dep.polyTape (dep.evalPts p)
          p r counter digitsFn)
      let ops₂ := parties₂.map (fun p =>
        computeShamirCustodianOpening dep.H dep.masterSeed dep.polyTape (dep.evalPts p)
          p r counter digitsFn)
      (∀ (c₀ : TowerElem 7) (tail : ShamirPadPoly (TowerElem 7) d),
        ringDot lambdas₁ ((parties₁.map dep.evalPts).map
          (fun x => RoundPoly.evalCoeffs (c₀ :: tail.1) x)) = c₀) →
      (∀ (c₀ : TowerElem 7) (tail : ShamirPadPoly (TowerElem 7) d),
        ringDot lambdas₂ ((parties₂.map dep.evalPts).map
          (fun x => RoundPoly.evalCoeffs (c₀ :: tail.1) x)) = c₀) →
      r.leaf < 2 ^ dep.height →
      r.leaf < 2 ^ 64 →
      counter.toNat < 2 ^ 16 →
      digits.length = L →
      ((digits.map Fin.val).foldr (· + ·) 0) = dep.targetSum →
      combinePreSteppedShamirValidatorSig L dep.targetSum dep.H pk dep.digitsOf
        leafChainPk lambdas₁ r counter (assembleSubmittedSharesFromOpenings ops₁) authPath =
      combinePreSteppedShamirValidatorSig L dep.targetSum dep.H pk dep.digitsOf
        leafChainPk lambdas₂ r counter (assembleSubmittedSharesFromOpenings ops₂) authPath) ∧
    -- (3) Adversarial share-corruption soundness along every multi-turn trace:
    (∀ (trace : List (ShamirCustodyTurn n L)) (entry : Custody.Intent × QuorumJortsSig),
      let st := runShamirCustodyTrace dep
        (ShamirCustodyNetworkState.init n L dep.height dep.maxWindow) trace
      entry ∈ st.combinedSignatures →
      let msg := intentCanonicalPayload entry.1
      let digits := dep.digitsOf (quorumCounterDigest dep.H
        (quorumMessageHash dep.H pk entry.2.leaf msg) entry.2.counter)
      verifyQuorumJortsSigAt L dep.targetSum dep.H pk dep.digitsOf msg entry.2 = true ∧
      (entry.2.nodes =
          (quorumJortsReferenceSign dep.H dep.masterSeed entry.2.leaf entry.2.counter
            digits entry.2.authPath).nodes ∨
       Nonempty (WotsChainCollisionWitness (quorumChainStep dep.H pk.pkSeed entry.2.leaf) 4) ∨
       Nonempty (HashCollision256 dep.H))) := by
  intro pk
  have hHonestCombine :
      ∀ (parties : List (Fin n)) (lambdas : List (TowerElem 7))
        (r : Custody.Intent) (counter : UInt32),
      let gLeaf := UInt64.ofNat r.leaf
      let msg := intentCanonicalPayload r
      let digits := dep.digitsOf (quorumCounterDigest dep.H (quorumMessageHash dep.H pk gLeaf msg) counter)
      let digitsFn : Fin L → Fin 4 := fun i => digits.getD i.1 ⟨0, by decide⟩
      let leafChainPk : Fin L → Digest256 := fun i =>
        wotsChainIter (quorumChainStep dep.H pk.pkSeed gLeaf) i.1 0 3
          (quorumStageChainSk dep.H dep.masterSeed gLeaf (UInt32.ofNat i.1))
      let authPath := quorumAuthPath dep.H pk.pkSeed
        (quorumHonestLeafDigest L dep.H dep.masterSeed) dep.height 0 gLeaf.toNat
      let openings := parties.map (fun p =>
        computeShamirCustodianOpening dep.H dep.masterSeed dep.polyTape (dep.evalPts p)
          p r counter digitsFn)
      (∀ (c₀ : TowerElem 7) (tail : ShamirPadPoly (TowerElem 7) d),
        ringDot lambdas ((parties.map dep.evalPts).map
          (fun x => RoundPoly.evalCoeffs (c₀ :: tail.1) x)) = c₀) →
      r.leaf < 2 ^ dep.height →
      r.leaf < 2 ^ 64 →
      counter.toNat < 2 ^ 16 →
      digits.length = L →
      ((digits.map Fin.val).foldr (· + ·) 0) = dep.targetSum →
      combinePreSteppedShamirValidatorSig L dep.targetSum dep.H pk dep.digitsOf
        leafChainPk lambdas r counter (assembleSubmittedSharesFromOpenings openings) authPath =
          some (quorumJortsReferenceSign dep.H dep.masterSeed gLeaf counter digits authPath) ∧
      verifyQuorumJortsSigAt L dep.targetSum dep.H pk dep.digitsOf msg
        (quorumJortsReferenceSign dep.H dep.masterSeed gLeaf counter digits authPath) = true := by
    intro parties lambdas r counter gLeaf msg digits digitsFn leafChainPk authPath openings
      hLag hLeafH hLeaf64 hCtr hDigLen hSum
    have hGLeafNat : gLeaf.toNat = r.leaf := by
      change (BitVec.ofNat 64 r.leaf).toNat = r.leaf
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hLeaf64]
    have hRefVer := quorumJortsReferenceSign_verifies L dep.targetSum dep.height hHeightLt
      dep.H dep.masterSeed dep.digitsOf gLeaf counter msg (hGLeafNat ▸ hLeafH) hCtr hDigLen hSum
    have hSelfVer := (preStepped_tower128_digest256_self_verification
      (quorumChainStep dep.H pk.pkSeed gLeaf)
      (fun i : Fin L => quorumStageChainSk dep.H dep.masterSeed gLeaf (UInt32.ofNat i.1))
      (dep.polyTape gLeaf) lambdas (parties.map dep.evalPts) hLag digitsFn).1
    have hSubEq : assembleSubmittedSharesFromOpenings openings =
        (fun i : Fin L =>
          if h : (digitsFn i).val < 3 then
            let k : Fin 3 := ⟨(digitsFn i).val, h⟩
            let trueNode := wotsChainIter (quorumChainStep dep.H pk.pkSeed gLeaf) i.1 0
              (digitsFn i).val (quorumStageChainSk dep.H dep.masterSeed gLeaf (UInt32.ofNat i.1))
            let (lo, hi) := splitDigest256Tower128 trueNode
            ((parties.map dep.evalPts).map (fun x => RoundPoly.evalCoeffs (lo :: (dep.polyTape gLeaf i k).1.1) x),
             (parties.map dep.evalPts).map (fun x => RoundPoly.evalCoeffs (hi :: (dep.polyTape gLeaf i k).2.1) x))
          else
            ([], [])) := by
      funext i
      unfold assembleSubmittedSharesFromOpenings
      dsimp only [openings, computeShamirCustodianOpening]
      by_cases hd : (digitsFn i).val < 3
      · simp only [hd, ↓reduceDIte]
        have hFst : ∀ ps : List (Fin n),
            (ps.map (fun p =>
              ({ party := p, intent := r, epoch := gLeaf, counter := counter,
                 evalPoint := dep.evalPts p,
                 chainShares := fun j =>
                   if hStep : (digitsFn j).val < 3 then
                     let k : Fin 3 := ⟨(digitsFn j).val, hStep⟩
                     let sk₀ := quorumStageChainSk dep.H dep.masterSeed gLeaf (UInt32.ofNat j.1)
                     let trueNode := wotsChainIter
                       (quorumChainStep dep.H (quorumStagePkSeed dep.H dep.masterSeed) gLeaf)
                       j.1 0 (digitsFn j).val sk₀
                     let (lo, hi) := splitDigest256Tower128 trueNode
                     some (RoundPoly.evalCoeffs (lo :: (dep.polyTape gLeaf j k).1.1) (dep.evalPts p),
                           RoundPoly.evalCoeffs (hi :: (dep.polyTape gLeaf j k).2.1) (dep.evalPts p))
                   else none } : ShamirCustodianShareOpening n L))).filterMap
              (fun op => (op.chainShares i).map Prod.fst) =
            (ps.map dep.evalPts).map (fun x =>
              RoundPoly.evalCoeffs
                ((splitDigest256Tower128
                  (wotsChainIter (quorumChainStep dep.H pk.pkSeed gLeaf) i.1 0 (digitsFn i).val
                    (quorumStageChainSk dep.H dep.masterSeed gLeaf (UInt32.ofNat i.1)))).1 ::
                 (dep.polyTape gLeaf i ⟨(digitsFn i).val, hd⟩).1.1) x) := by
          intro ps
          induction ps with
          | nil => rfl
          | cons p rest ih =>
            simp only [List.map_cons, List.filterMap_cons, hd, ↓reduceDIte, Option.map_some]
            exact congrArg _ ih
        have hSnd : ∀ ps : List (Fin n),
            (ps.map (fun p =>
              ({ party := p, intent := r, epoch := gLeaf, counter := counter,
                 evalPoint := dep.evalPts p,
                 chainShares := fun j =>
                   if hStep : (digitsFn j).val < 3 then
                     let k : Fin 3 := ⟨(digitsFn j).val, hStep⟩
                     let sk₀ := quorumStageChainSk dep.H dep.masterSeed gLeaf (UInt32.ofNat j.1)
                     let trueNode := wotsChainIter
                       (quorumChainStep dep.H (quorumStagePkSeed dep.H dep.masterSeed) gLeaf)
                       j.1 0 (digitsFn j).val sk₀
                     let (lo, hi) := splitDigest256Tower128 trueNode
                     some (RoundPoly.evalCoeffs (lo :: (dep.polyTape gLeaf j k).1.1) (dep.evalPts p),
                           RoundPoly.evalCoeffs (hi :: (dep.polyTape gLeaf j k).2.1) (dep.evalPts p))
                   else none } : ShamirCustodianShareOpening n L))).filterMap
              (fun op => (op.chainShares i).map Prod.snd) =
            (ps.map dep.evalPts).map (fun x =>
              RoundPoly.evalCoeffs
                ((splitDigest256Tower128
                  (wotsChainIter (quorumChainStep dep.H pk.pkSeed gLeaf) i.1 0 (digitsFn i).val
                    (quorumStageChainSk dep.H dep.masterSeed gLeaf (UInt32.ofNat i.1)))).2 ::
                 (dep.polyTape gLeaf i ⟨(digitsFn i).val, hd⟩).2.1) x) := by
          intro ps
          induction ps with
          | nil => rfl
          | cons p rest ih =>
            simp only [List.map_cons, List.filterMap_cons, hd, ↓reduceDIte, Option.map_some]
            exact congrArg _ ih
        exact Prod.ext (hFst parties) (hSnd parties)
      · simp only [hd, ↓reduceDIte]
        have hNilFst : ∀ ps : List (Fin n),
            (ps.map (fun p =>
              ({ party := p, intent := r, epoch := gLeaf, counter := counter,
                 evalPoint := dep.evalPts p,
                 chainShares := fun j =>
                   if hStep : (digitsFn j).val < 3 then
                     let k : Fin 3 := ⟨(digitsFn j).val, hStep⟩
                     let sk₀ := quorumStageChainSk dep.H dep.masterSeed gLeaf (UInt32.ofNat j.1)
                     let trueNode := wotsChainIter
                       (quorumChainStep dep.H (quorumStagePkSeed dep.H dep.masterSeed) gLeaf)
                       j.1 0 (digitsFn j).val sk₀
                     let (lo, hi) := splitDigest256Tower128 trueNode
                     some (RoundPoly.evalCoeffs (lo :: (dep.polyTape gLeaf j k).1.1) (dep.evalPts p),
                           RoundPoly.evalCoeffs (hi :: (dep.polyTape gLeaf j k).2.1) (dep.evalPts p))
                   else none } : ShamirCustodianShareOpening n L))).filterMap
              (fun op => (op.chainShares i).map Prod.fst) = [] := by
          intro ps
          induction ps with
          | nil => rfl
          | cons p rest ih =>
            simp only [List.map_cons, List.filterMap_cons, hd, ↓reduceDIte, Option.map_none]
            exact ih
        have hNilSnd : ∀ ps : List (Fin n),
            (ps.map (fun p =>
              ({ party := p, intent := r, epoch := gLeaf, counter := counter,
                 evalPoint := dep.evalPts p,
                 chainShares := fun j =>
                   if hStep : (digitsFn j).val < 3 then
                     let k : Fin 3 := ⟨(digitsFn j).val, hStep⟩
                     let sk₀ := quorumStageChainSk dep.H dep.masterSeed gLeaf (UInt32.ofNat j.1)
                     let trueNode := wotsChainIter
                       (quorumChainStep dep.H (quorumStagePkSeed dep.H dep.masterSeed) gLeaf)
                       j.1 0 (digitsFn j).val sk₀
                     let (lo, hi) := splitDigest256Tower128 trueNode
                     some (RoundPoly.evalCoeffs (lo :: (dep.polyTape gLeaf j k).1.1) (dep.evalPts p),
                           RoundPoly.evalCoeffs (hi :: (dep.polyTape gLeaf j k).2.1) (dep.evalPts p))
                   else none } : ShamirCustodianShareOpening n L))).filterMap
              (fun op => (op.chainShares i).map Prod.snd) = [] := by
          intro ps
          induction ps with
          | nil => rfl
          | cons p rest ih =>
            simp only [List.map_cons, List.filterMap_cons, hd, ↓reduceDIte, Option.map_none]
            exact ih
        exact Prod.ext (hNilFst parties) (hNilSnd parties)
    unfold combinePreSteppedShamirValidatorSig
    dsimp only
    rw [hSubEq]
    change (match preSteppedDigest256ReconstructAndSelfVerify
        (quorumChainStep dep.H pk.pkSeed gLeaf) leafChainPk lambdas digitsFn _ with
      | none => none
      | some candFn => _) = _ ∧ _
    rw [hSelfVer]
    dsimp only
    have hSigEq :
        ({ leaf := gLeaf
           counter := counter
           nodes := (List.finRange L).map (fun i : Fin L =>
             wotsChainIter (quorumChainStep dep.H pk.pkSeed gLeaf) i.1 0 (digitsFn i).val
               (quorumStageChainSk dep.H dep.masterSeed gLeaf (UInt32.ofNat i.1)))
           authPath := authPath } : QuorumJortsSig) =
        quorumJortsReferenceSign dep.H dep.masterSeed gLeaf counter digits authPath := by
      unfold quorumJortsReferenceSign
      congr 1
      apply List.ext_getElem
      · simp [hDigLen]
      · intro k hk1 hk2
        simp only [List.getElem_map, List.getElem_finRange]
        dsimp only [digitsFn, pk, ShamirValidatorDeployment.validatorPk, deriveQuorumValidatorPublicKey]
        rw [list_getD_eq_getElem_local digits _ (by simp at hk1; omega)]
        simp
    have hRefVer' :
        verifyQuorumJortsSigAt L dep.targetSum dep.H pk dep.digitsOf (intentCanonicalPayload r)
          (quorumJortsReferenceSign dep.H dep.masterSeed gLeaf counter digits authPath) = true :=
      hRefVer
    rw [hSigEq, hRefVer']
    exact ⟨rfl, rfl⟩
  refine ⟨hHonestCombine, ?_, ?_⟩
  · -- Part 2: Quorum invariance across (parties₁, lambdas₁) and (parties₂, lambdas₂)
    intro p₁ p₂ l₁ l₂ r counter _ _ _ _ _ _ _ _ hLag₁ hLag₂ hLH hL64 hCtr hDL hS
    have h1 := (hHonestCombine p₁ l₁ r counter hLag₁ hLH hL64 hCtr hDL hS).1
    have h2 := (hHonestCombine p₂ l₂ r counter hLag₂ hLH hL64 hCtr hDL hS).1
    exact h1.trans h2.symm
  · -- Part 3: Multi-turn combined signature verification & constructive collision extraction
    intro trace entry st hMem msg digits
    have hInv := runShamirCustodyTrace_inv dep trace
    have hVer := (hInv.combinedVerified entry hMem).2
    refine ⟨hVer, ?_⟩
    cases verifyQuorumJortsSigAt_extract_reference_or_collision L dep.targetSum dep.height
        hHeightLt hChainBound dep.H dep.masterSeed dep.digitsOf msg entry.2 hVer with
    | inl hEqNodes => exact .inl hEqNodes
    | inr sub =>
      cases sub with
      | inl w => exact .inr (.inl ⟨w⟩)
      | inr c => exact .inr (.inr ⟨c⟩)

/-- **Crown Jewel 2B (`M3` + `M7` Production Hypertree Single-Validator Bridge) —
    (`shamir_custody_single_validator_pq_bridge`)**:
    Connects single-validator threshold MPC signing (`mpcEvalProductionStatefulSign` under a
    **single** enrolled `validatorSk : PqSecretKey`, `o.MatchesKey cfg.suite validatorSk`) to
    both `CompleteMediationBoundary` custodian vaults AND `ProdCollisionExtraction` /
    `ProdHashGameReductions`:
    1. **Single-Validator MPC Equivalence & Verification:** For every `r` signed via
       `mpcEvalProductionStatefulSign`, the output equals `evalProductionStatefulSign` and
       verifies under the **single** enrolled `derivePublicKey cfg.suite cfg.params validatorSk`!
    2. **Unapproved Forgery Extraction (`f < t`):** If `t` custodian approvals are required
       (`maskCard Corrupt ≤ f < t`) for a subset `S` (`t ≤ maskCard S`), then there is an honest
       custodian `h ∈ S \ Corrupt` whose vault satisfies `queries_one_time`. Whenever any
       `sigStar` verifies under the single enrolled `derivePublicKey cfg.suite cfg.params validatorSk`
       on `intentCanonicalPayload rStar` while `rStar ∉ (st.vaults h).attempted` (never released
       by honest custodian `h`, where the validator's signing history is recorded in `(st.vaults h)`),
       it wins `prodEufCmaWin` AND constructively yields `Nonempty (ProdTcrWitness ...)` or
       `ProdPreimageBreak ...` (`0 Classical.choice`)! -/
