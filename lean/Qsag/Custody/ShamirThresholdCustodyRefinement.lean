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
