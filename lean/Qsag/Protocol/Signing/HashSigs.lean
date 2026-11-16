module
/-
# Qsag.Protocol.Signing.HashSigs — Unified Tweakable-Hash Signatures (`Corduroy`, `Baggy`, `Jorts`)

Self-contained Lean 4.35 formalization of tweakable-hash post-quantum signatures, constructive
`PSum` forgery extraction (`0 Classical.choice`), classical+PQ hybrid combiners, and canonical
wire-format verification:
1. 32-byte big-endian `HashAdrs` address framing (`encodeAdrs_injective`).
2. `TweakableHashSuite` (`cshake256Suite`, `poseidon2Suite`) with injective `encodeMultiFrame`
   domain separation (`thCall_binds_or_collision`).
3. Target-sum Winternitz (`TSW` / `WOTS+C`) incomparable digit encoding
   (`tsw_incomparable_no_chain_forgery`) and chain composition (`wotsChainSteps_add`).
4. Parametric binary Merkle & FORS authentication (`walkMerkleAuthPath_buildMerkleAuthPath`,
   `recoverForsPk_buildForsOpenings`).
5. Unified `Corduroy-Custody-128`, `Baggy-128f`, and `Jorts-Poseidon2` engine
   (`verifyPqHashSig_evalSingleSign`), constructive `0 Classical` `PSum` EUF-CMA extractor
   (`extractPqHashForgery`), and `ValidJortsBatch`.
6. Committed-identity classical+PQ hybrid combiner (`hybrid_ucRealizes_if_either_secure`,
   `hybrid_partner_substitution_rejected`) and `"QSAG\x01"` tri-state wire verifier
   (`verifyWire_malformed_iff`).
-/

public import Qsag.Math.Goldilocks
public import Qsag.Oracle.Keccak
public import Qsag.Oracle.Poseidon2
public import Qsag.Protocol.Aggregation.UcGames

import Qsag.Tactic.AssuranceKit

public section
namespace Qsag

set_option autoImplicit false

/-! ## 1. Pre-Locked 32-Byte Big-Endian `HashAdrs` Framing (`encodeAdrs_injective`) -/

/-- Domain-separation role of a 32-byte hash address inside the hypertree / FORS / PORS+FP / WOTS+C hierarchy
    (`crates/qsag-core/src/tsw_baggy.rs:39-74` and `pors_fp.rs:241-248`). -/
inductive AdrsKind where
  | wotsHash | wotsPk | tree | forsTree | forsRoots | wotsPrf | forsPrf | porsPrf | porsTree
  deriving DecidableEq, Repr, Inhabited

/-- Canonical 32-bit wire tag for `AdrsKind` (`0..=8`). -/
def AdrsKind.toCode : AdrsKind → UInt32
  | .wotsHash => 0 | .wotsPk => 1 | .tree => 2 | .forsTree => 3
  | .forsRoots => 4 | .wotsPrf => 5 | .forsPrf => 6
  | .porsPrf => 7 | .porsTree => 8

/-- Checked inverse of `AdrsKind.toCode` matching `AdrsKind::from_code` (`tsw_baggy.rs:60-73`). -/
def AdrsKind.fromCode : UInt32 → Option AdrsKind
  | 0 => some .wotsHash | 1 => some .wotsPk | 2 => some .tree | 3 => some .forsTree
  | 4 => some .forsRoots | 5 => some .wotsPrf | 6 => some .forsPrf
  | 7 => some .porsPrf | 8 => some .porsTree | _ => none

theorem AdrsKind.fromCode_toCode (k : AdrsKind) : AdrsKind.fromCode k.toCode = some k := by
  cases k <;> rfl

theorem AdrsKind.toCode_pors :
    AdrsKind.porsPrf.toCode = 7 ∧ AdrsKind.porsTree.toCode = 8 ∧
    AdrsKind.fromCode 7 = some .porsPrf ∧ AdrsKind.fromCode 8 = some .porsTree ∧
    AdrsKind.fromCode 9 = none := by
  decide

theorem AdrsKind.toCode_injective {k₁ k₂ : AdrsKind} (h : k₁.toCode = k₂.toCode) : k₁ = k₂ := by
  cases k₁ <;> cases k₂ <;> first | rfl | cases h

/-- Canonical 32-byte tweakable hash address (`ADRS`):
    `[0..4) layer || [4..8) 0 || [8..16) tree || [16..20) kind || [20..24) keyPair || [24..28) chainIdx || [28..32) hashStep`. -/
structure HashAdrs where
  layer    : UInt32
  tree     : UInt64
  kind     : AdrsKind
  keyPair  : UInt32
  chainIdx : UInt32
  hashStep : UInt32
  deriving DecidableEq, Repr

/-- Encode `HashAdrs` into its exact 32-byte big-endian frame. -/
@[expose] def encodeAdrs (a : HashAdrs) : List UInt8 :=
  be 4 a.layer.toNat ++ (be 4 0 ++ (be 8 a.tree.toNat ++
    (be 4 a.kind.toCode.toNat ++ (be 4 a.keyPair.toNat ++
      (be 4 a.chainIdx.toNat ++ be 4 a.hashStep.toNat)))))

theorem encodeAdrs_length (a : HashAdrs) : (encodeAdrs a).length = 32 := by
  simp [encodeAdrs, length_be]

theorem uint32_eq_of_be4_eq {x y : UInt32} (h : be 4 x.toNat = be 4 y.toNat) : x = y := by
  have hx : x.toNat < 256 ^ 4 := by simpa using x.toBitVec.isLt
  have hy : y.toNat < 256 ^ 4 := by simpa using y.toBitVec.isLt
  exact UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq (be_injective hx hy h))

theorem uint64_eq_of_be8_eq {x y : UInt64} (h : be 8 x.toNat = be 8 y.toNat) : x = y := by
  have hx : x.toNat < 256 ^ 8 := by simpa using x.toBitVec.isLt
  have hy : y.toNat < 256 ^ 8 := by simpa using y.toBitVec.isLt
  exact UInt64.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq (be_injective hx hy h))

/-- **Pre-Locked `ADRS` Framing Injectivity (`encodeAdrs_injective`)**:
    Distinct `HashAdrs` values never collide before hashing. -/
theorem encodeAdrs_injective {a₁ a₂ : HashAdrs} (h : encodeAdrs a₁ = encodeAdrs a₂) : a₁ = a₂ := by
  unfold encodeAdrs at h
  obtain ⟨hLayer, h1⟩ := List.append_inj h (by simp [length_be])
  obtain ⟨_, h2⟩ := List.append_inj h1 (by simp [length_be])
  obtain ⟨hTree, h3⟩ := List.append_inj h2 (by simp [length_be])
  obtain ⟨hKind, h4⟩ := List.append_inj h3 (by simp [length_be])
  obtain ⟨hKp, h5⟩ := List.append_inj h4 (by simp [length_be])
  obtain ⟨hChain, hStep⟩ := List.append_inj h5 (by simp [length_be])
  cases a₁; cases a₂; simp only [HashAdrs.mk.injEq]
  exact ⟨uint32_eq_of_be4_eq hLayer, uint64_eq_of_be8_eq hTree,
         AdrsKind.toCode_injective (uint32_eq_of_be4_eq hKind),
         uint32_eq_of_be4_eq hKp, uint32_eq_of_be4_eq hChain, uint32_eq_of_be4_eq hStep⟩

/-! ## 2. Polymorphic `TweakableHashSuite` (`cshake256Suite` & `poseidon2Suite`) -/

/-- Polymorphic 256-bit tweakable hash suite abstracting `cSHAKE256` and `Poseidon2` over Goldilocks. -/
structure TweakableHashSuite where
  suiteId     : List UInt8
  rawHash     : Hash
  rawHash_len : ∀ msg : List UInt8, (rawHash msg).length = 32

def pqCshakeSuiteCustom : List UInt8 := "QSAG.PQ.SUITE.CSHAKE256/v1".toUTF8.toList
def pqPoseidon2SuiteId  : List UInt8 := "QSAG.PQ.SUITE.POSEIDON2/v1".toUTF8.toList

/-- NIST SP 800-185 `cSHAKE256` instantiation (`Corduroy` / `Baggy-cSHAKE256`). -/
@[expose] def cshake256Suite : TweakableHashSuite where
  suiteId := pqCshakeSuiteCustom
  rawHash := cshake256Bytes pqCshakeSuiteCustom
  rawHash_len := cshake256Bytes_length pqCshakeSuiteCustom

/-- Width-12 Goldilocks `Poseidon2` algebraic instantiation (`Jorts` / `Corduroy-Poseidon2`). -/
@[expose] def poseidon2Suite : TweakableHashSuite where
  suiteId := pqPoseidon2SuiteId
  rawHash := poseidon2Hash32
  rawHash_len := poseidon2Hash32_length

def tagPrfMsg : List UInt8 := "QSAG.PQ.PRFMSG/v1".toUTF8.toList
def tagHMsg   : List UInt8 := [81, 83, 65, 71, 46, 80, 81, 46, 72, 77, 83, 71, 47, 118, 49]
def tagPrf    : List UInt8 := "QSAG.PQ.PRF/v1".toUTF8.toList
def tagThF    : List UInt8 := "QSAG.PQ.TH_F/v1".toUTF8.toList
def tagThH    : List UInt8 := "QSAG.PQ.TH_H/v1".toUTF8.toList
theorem tagThH_eq : tagThH = "QSAG.PQ.TH_H/v1".toUTF8.toList := by rfl
def tagThTl   : List UInt8 := "QSAG.PQ.TH_TL/v1".toUTF8.toList
def tagHPre   : List UInt8 := "QSAG.PQ.PRE/v1".toUTF8.toList

/- QSAG.PQ.HINT/v1 -/
def tagHInternal : List UInt8 := [81, 83, 65, 71, 46, 80, 81, 46, 72, 73, 78, 84, 47, 118, 49]

/- QSAG.PQ.HXOF/v1 -/
def tagHXof : List UInt8 := [81, 83, 65, 71, 46, 80, 81, 46, 72, 88, 79, 70, 47, 118, 49]

/-- Self-delimiting preimage for any tweakable hash call `(roleTag, pkSeed, adrs, args)`. -/
def thPreimage (roleTag pkSeed : List UInt8) (adrs : HashAdrs) (args : List (List UInt8)) : List UInt8 :=
  encodeMultiFrame ([roleTag, pkSeed, encodeAdrs adrs] ++ args)

/-- Evaluate a tweakable hash call with full `ADRS` and `pkSeed` domain separation. -/
def thCall (suite : TweakableHashSuite) (roleTag pkSeed : List UInt8)
    (adrs : HashAdrs) (args : List (List UInt8)) : List UInt8 :=
  suite.rawHash (thPreimage roleTag pkSeed adrs args)

theorem thCall_length (suite : TweakableHashSuite) (roleTag pkSeed : List UInt8)
    (adrs : HashAdrs) (args : List (List UInt8)) :
    (thCall suite roleTag pkSeed adrs args).length = 32 :=
  suite.rawHash_len _

theorem thPreimage_injective {t₁ p₁ : List UInt8} {a₁ : HashAdrs} {xs₁ : List (List UInt8)}
    {t₂ p₂ : List UInt8} {a₂ : HashAdrs} {xs₂ : List (List UInt8)}
    (h : thPreimage t₁ p₁ a₁ xs₁ = thPreimage t₂ p₂ a₂ xs₂) :
    t₁ = t₂ ∧ p₁ = p₂ ∧ a₁ = a₂ ∧ xs₁ = xs₂ := by
  have hList := encodeMultiFrame_injective h
  simp only [List.cons_append, List.nil_append, List.cons.injEq] at hList
  rcases hList with ⟨ht, hp, ha, hxs⟩
  exact ⟨ht, hp, encodeAdrs_injective ha, hxs⟩

/-- Constructive `0 Classical` collision binder for `thCall`. -/
def thCall_binds_or_collision (suite : TweakableHashSuite)
    {t₁ p₁ : List UInt8} {a₁ : HashAdrs} {xs₁ : List (List UInt8)}
    {t₂ p₂ : List UInt8} {a₂ : HashAdrs} {xs₂ : List (List UInt8)}
    (hEq : thCall suite t₁ p₁ a₁ xs₁ = thCall suite t₂ p₂ a₂ xs₂) :
    PSum (t₁ = t₂ ∧ p₁ = p₂ ∧ a₁ = a₂ ∧ xs₁ = xs₂)
         (HashCollisionWitness suite.rawHash) :=
  if hPre : thPreimage t₁ p₁ a₁ xs₁ = thPreimage t₂ p₂ a₂ xs₂ then
    .inl (thPreimage_injective hPre)
  else
    .inr { m1 := thPreimage t₁ p₁ a₁ xs₁
           m2 := thPreimage t₂ p₂ a₂ xs₂
           ne := hPre
           eq := hEq }

def thChainF (suite : TweakableHashSuite) (pkSeed : List UInt8) (adrs : HashAdrs) (x : List UInt8) : List UInt8 :=
  thCall suite tagThF pkSeed adrs [x]

def thNodeH (suite : TweakableHashSuite) (pkSeed : List UInt8) (adrs : HashAdrs) (l r : List UInt8) : List UInt8 :=
  thCall suite tagThH pkSeed adrs [l, r]

def thTweakTl (suite : TweakableHashSuite) (pkSeed : List UInt8) (adrs : HashAdrs) (limbs : List (List UInt8)) : List UInt8 :=
  thCall suite tagThTl pkSeed adrs limbs

def thSecretPrf (suite : TweakableHashSuite) (pkSeed skSeed : List UInt8) (adrs : HashAdrs) : List UInt8 :=
  thCall suite tagPrf pkSeed adrs [skSeed]

def zeroAdrs : HashAdrs := ⟨0, 0, .wotsHash, 0, 0, 0⟩

def thPrfMsg (suite : TweakableHashSuite) (skPrf optRand mu : List UInt8) : List UInt8 :=
  thCall suite tagPrfMsg [] zeroAdrs [skPrf, optRand, mu]

def thPreHash (suite : TweakableHashSuite) (pkSeed pkRoot msg : List UInt8) : List UInt8 :=
  thCall suite tagHPre pkSeed zeroAdrs [pkRoot, msg]

/-- 64-byte XOF message/node digest binding `(layerIdx, treeIdx, kpIdx, ctr)` in `HashAdrs`:
    concatenates two domain-separated 32-byte `thCall` blocks (`chainIdx = 0, 1`) so 128-chain
    (`256`-bit) base-4 `TSW` digits and FORS bit windows (`88 + k * a ≤ 512` bits) never wrap! -/
def thHashMsg (suite : TweakableHashSuite) (rRand pkSeed pkRoot mu : List UInt8)
    (layerIdx : UInt32) (treeIdx : UInt64) (kpIdx : UInt32) (ctr : Nat) : List UInt8 :=
  let b0 := thCall suite tagHMsg pkSeed ⟨layerIdx, treeIdx, .wotsHash, kpIdx, 0, UInt32.ofNat ctr⟩ [rRand, pkRoot, mu, be 4 ctr]
  let b1 := thCall suite tagHMsg pkSeed ⟨layerIdx, treeIdx, .wotsHash, kpIdx, 1, UInt32.ofNat ctr⟩ [rRand, pkRoot, mu, be 4 ctr]
  b0 ++ b1

/-- Production stateful leaf-message digest: single 32-byte `H_MSG` call at `layer = 0, chainIdx = 0`
    matching `crates/qsag-core/src/tsw_baggy.rs::th_hash_leaf_msg`. -/
def thHashLeafMsg (suite : TweakableHashSuite) (rRand pkSeed pkRoot mu : List UInt8)
    (treeIdx : UInt64) (kpIdx : UInt32) (ctr : Nat) : List UInt8 :=
  thCall suite tagHMsg pkSeed
    ⟨0, treeIdx, .wotsHash, kpIdx, 0, UInt32.ofNat ctr⟩ [rRand, pkRoot, mu, be 4 ctr]

/-- Production internal-node digest: no message randomness and one 32-byte HINT call. -/
def thHashInternalNode (suite : TweakableHashSuite) (pkSeed pkRoot nodeRoot : List UInt8)
    (layer : UInt32) (tree : UInt64) (kp : UInt32) (ctr : Nat) : List UInt8 :=
  thCall suite tagHInternal pkSeed
    ⟨layer, tree, .wotsHash, kp, 0, UInt32.ofNat ctr⟩ [pkRoot, nodeRoot, be 4 ctr]

def thXofMsgBlocks (suite : TweakableHashSuite) (rRand pkSeed pkRoot mu : List UInt8)
    (first : Nat) : Nat → List UInt8
  | 0 => []
  | n + 1 =>
    thCall suite tagHXof pkSeed
      ⟨0, 0, .forsRoots, 0, 0, UInt32.ofNat first⟩ [rRand, pkRoot, mu, be 4 first] ++
      thXofMsgBlocks suite rRand pkSeed pkRoot mu (first + 1) n

/-- Production counter-mode HXOF with exactly the requested number of bytes. -/
def thXofMsg (suite : TweakableHashSuite) (rRand pkSeed pkRoot mu : List UInt8)
    (outLen : Nat) : List UInt8 :=
  (thXofMsgBlocks suite rRand pkSeed pkRoot mu 0 ((outLen + 31) / 32)).take outLen

theorem thXofMsgBlocks_zero (suite : TweakableHashSuite) (rRand pkSeed pkRoot mu : List UInt8)
    (first : Nat) : thXofMsgBlocks suite rRand pkSeed pkRoot mu first 0 = [] := by rfl

theorem thXofMsgBlocks_succ (suite : TweakableHashSuite) (rRand pkSeed pkRoot mu : List UInt8)
    (first n : Nat) :
    thXofMsgBlocks suite rRand pkSeed pkRoot mu first (n + 1) =
      thCall suite tagHXof pkSeed
        ⟨0, 0, .forsRoots, 0, 0, UInt32.ofNat first⟩ [rRand, pkRoot, mu, be 4 first] ++
      thXofMsgBlocks suite rRand pkSeed pkRoot mu (first + 1) n := by rfl

theorem thXofMsg_eq (suite : TweakableHashSuite) (rRand pkSeed pkRoot mu : List UInt8)
    (outLen : Nat) :
    thXofMsg suite rRand pkSeed pkRoot mu outLen =
      (thXofMsgBlocks suite rRand pkSeed pkRoot mu 0 ((outLen + 31) / 32)).take outLen := by rfl

private theorem thXofMsgBlocks_length (suite : TweakableHashSuite)
    (rRand pkSeed pkRoot mu : List UInt8) (n first : Nat) :
    (thXofMsgBlocks suite rRand pkSeed pkRoot mu first n).length = 32 * n := by
  induction n generalizing first with
  | zero => rfl
  | succ n ih =>
    simp only [thXofMsgBlocks, List.length_append, thCall_length, ih]
    omega

theorem thXofMsg_length (suite : TweakableHashSuite) (rRand pkSeed pkRoot mu : List UInt8)
    (n : Nat) : (thXofMsg suite rRand pkSeed pkRoot mu n).length = n := by
  simp only [thXofMsg, List.length_take, thXofMsgBlocks_length]
  apply Nat.min_eq_left
  omega

theorem thHashLeafMsg_length (suite : TweakableHashSuite) (rRand pkSeed pkRoot mu : List UInt8)
    (treeIdx : UInt64) (kpIdx : UInt32) (ctr : Nat) :
    (thHashLeafMsg suite rRand pkSeed pkRoot mu treeIdx kpIdx ctr).length = 32 :=
  thCall_length _ _ _ _ _

theorem thHashLeafMsg_eq (suite : TweakableHashSuite) (rRand pkSeed pkRoot mu : List UInt8)
    (treeIdx : UInt64) (kpIdx : UInt32) (ctr : Nat) :
    thHashLeafMsg suite rRand pkSeed pkRoot mu treeIdx kpIdx ctr =
      thCall suite tagHMsg pkSeed
        ⟨0, treeIdx, .wotsHash, kpIdx, 0, UInt32.ofNat ctr⟩ [rRand, pkRoot, mu, be 4 ctr] := by rfl

theorem thHashInternalNode_length (suite : TweakableHashSuite) (pkSeed pkRoot nodeRoot : List UInt8)
    (layer : UInt32) (tree : UInt64) (kp : UInt32) (ctr : Nat) :
    (thHashInternalNode suite pkSeed pkRoot nodeRoot layer tree kp ctr).length = 32 :=
  thCall_length _ _ _ _ _

theorem thHashInternalNode_eq (suite : TweakableHashSuite) (pkSeed pkRoot nodeRoot : List UInt8)
    (layer : UInt32) (tree : UInt64) (kp : UInt32) (ctr : Nat) :
    thHashInternalNode suite pkSeed pkRoot nodeRoot layer tree kp ctr =
      thCall suite tagHInternal pkSeed
        ⟨layer, tree, .wotsHash, kp, 0, UInt32.ofNat ctr⟩ [pkRoot, nodeRoot, be 4 ctr] := by rfl

/-- HINT cannot be mistaken for the legacy HMSG preimage before hashing. -/
theorem internal_message_domain_separated (pkSeed : List UInt8) (a b : HashAdrs)
    (xs ys : List (List UInt8)) :
    thPreimage tagHInternal pkSeed a xs ≠ thPreimage tagHMsg pkSeed b ys := by
  intro h
  have ht := (thPreimage_injective h).1
  have hn : tagHInternal ≠ tagHMsg := by decide +kernel
  exact hn ht

theorem thHashMsg_length (suite : TweakableHashSuite) (rRand pkSeed pkRoot mu : List UInt8)
    (layerIdx : UInt32) (treeIdx : UInt64) (kpIdx : UInt32) (ctr : Nat) :
    (thHashMsg suite rRand pkSeed pkRoot mu layerIdx treeIdx kpIdx ctr).length = 64 := by
  simp [thHashMsg, thCall_length]

theorem thPreimage_eq (roleTag pkSeed : List UInt8) (adrs : HashAdrs) (args : List (List UInt8)) :
    thPreimage roleTag pkSeed adrs args = encodeMultiFrame ([roleTag, pkSeed, encodeAdrs adrs] ++ args) := by rfl
theorem thCall_eq (suite : TweakableHashSuite) (roleTag pkSeed : List UInt8) (adrs : HashAdrs) (args : List (List UInt8)) :
    thCall suite roleTag pkSeed adrs args = suite.rawHash (thPreimage roleTag pkSeed adrs args) := by rfl
theorem thNodeH_eq (suite : TweakableHashSuite) (pkSeed : List UInt8) (adrs : HashAdrs) (l r : List UInt8) :
    thNodeH suite pkSeed adrs l r = thCall suite tagThH pkSeed adrs [l, r] := by rfl
theorem thChainF_eq (suite : TweakableHashSuite) (pkSeed : List UInt8) (adrs : HashAdrs) (x : List UInt8) :
    thChainF suite pkSeed adrs x = thCall suite tagThF pkSeed adrs [x] := by rfl
theorem thSecretPrf_eq (suite : TweakableHashSuite) (pkSeed skSeed : List UInt8) (adrs : HashAdrs) :
    thSecretPrf suite pkSeed skSeed adrs = thCall suite tagPrf pkSeed adrs [skSeed] := by rfl
theorem thPrfMsg_eq (suite : TweakableHashSuite) (skPrf optRand mu : List UInt8) :
    thPrfMsg suite skPrf optRand mu = thCall suite tagPrfMsg [] zeroAdrs [skPrf, optRand, mu] := by rfl

/-! ## 3. Target-Sum Winternitz (`TSW` / `WOTS+C`) & Incomparability Theorem -/

/-- Sum of base-`w` message digits. -/
def sumDigits : List Nat → Nat
  | [] => 0
  | d :: ds => d + sumDigits ds

/-- Canonical `TSW` target sum `⌊ell1 * (w - 1) / 2⌋` eliminating checksum chains. -/
def canonicalTargetSum (w ell1 : Nat) : Nat :=
  (ell1 * (w - 1)) / 2

theorem canonicalTargetSum_eq (w ell1 : Nat) :
    canonicalTargetSum w ell1 = (ell1 * (w - 1)) / 2 := by rfl

/-- **Load-Bearing `TSW` Checker (`checkTargetSum`)**:
    Verifies exact chain count `ell1`, range `∀ d, d < w`, and constant sum `sumDigits digits = target`. -/
@[expose] def checkTargetSum (w ell1 target : Nat) (digits : List Nat) : Bool :=
  decide (digits.length = ell1) &&
  digits.all (fun d => decide (d < w)) &&
  decide (sumDigits digits = target)

theorem checkTargetSum_iff (w ell1 target : Nat) (digits : List Nat) :
    checkTargetSum w ell1 target digits = true ↔
      digits.length = ell1 ∧ (∀ d ∈ digits, d < w) ∧ sumDigits digits = target := by
  simp only [checkTargetSum, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, and_assoc]

private theorem exists_lt_coord_of_sum_le_and_ne :
    ∀ (d₁ d₂ : List Nat),
      d₁.length = d₂.length →
      sumDigits d₁ ≤ sumDigits d₂ →
      (sumDigits d₁ < sumDigits d₂ ∨ d₁ ≠ d₂) →
      ∃ (r : Nat) (hr₁ : r < d₁.length) (hr₂ : r < d₂.length), d₁[r]'hr₁ < d₂[r]'hr₂
  | [], [], _, hLe, hOr => by
    simp only [sumDigits] at hLe hOr
    rcases hOr with hLt | hNe
    · omega
    · exact False.elim (hNe rfl)
  | x :: xs, y :: ys, hLen, hLe, hOr => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hLen
    simp only [sumDigits] at hLe hOr
    if hxy : x < y then
      exact ⟨0, Nat.zero_lt_succ _, Nat.zero_lt_succ _, hxy⟩
    else
      have hRestLe : sumDigits xs ≤ sumDigits ys := by omega
      have hRestOr : sumDigits xs < sumDigits ys ∨ xs ≠ ys := by
        if hyx : y < x then
          exact .inl (by omega)
        else
          have hEqXY : x = y := by omega
          subst hEqXY
          rcases hOr with hLt | hNe
          · exact .inl (by omega)
          · exact .inr (fun hEqXs => hNe (congrArg (x :: ·) hEqXs))
      obtain ⟨r, hr1, hr2, hStrict⟩ := exists_lt_coord_of_sum_le_and_ne xs ys hLen hRestLe hRestOr
      exact ⟨r + 1, Nat.succ_lt_succ hr1, Nat.succ_lt_succ hr2, hStrict⟩

/-- **Target-Sum Winternitz Incomparability Theorem (`tsw_incomparable_no_chain_forgery`)**:
    For ANY two distinct `TSW`-valid digit vectors `d₁ ≠ d₂`, `d₁` and `d₂` are strictly incomparable
    componentwise: there exists `r` with `d₁[r] < d₂[r]` AND `r'` with `d₂[r'] < d₁[r']`. -/
theorem tsw_incomparable_no_chain_forgery
    {w ell1 target : Nat} {d₁ d₂ : List Nat}
    (hValid₁ : checkTargetSum w ell1 target d₁ = true)
    (hValid₂ : checkTargetSum w ell1 target d₂ = true)
    (hDistinct : d₁ ≠ d₂) :
    (∃ (r : Nat) (hr₁ : r < d₁.length) (hr₂ : r < d₂.length),
      d₁[r]'hr₁ < d₂[r]'hr₂ ∧ d₂[r]'hr₂ < w) ∧
    (∃ (r' : Nat) (hr₂ : r' < d₂.length) (hr₁ : r' < d₁.length),
      d₂[r']'hr₂ < d₁[r']'hr₁ ∧ d₁[r']'hr₁ < w) := by
  obtain ⟨hLen₁, hBound₁, hSum₁⟩ := (checkTargetSum_iff w ell1 target d₁).mp hValid₁
  obtain ⟨hLen₂, hBound₂, hSum₂⟩ := (checkTargetSum_iff w ell1 target d₂).mp hValid₂
  have hLenEq : d₁.length = d₂.length := hLen₁.trans hLen₂.symm
  have hSumEq : sumDigits d₁ = sumDigits d₂ := hSum₁.trans hSum₂.symm
  obtain ⟨r, hr1, hr2, hLt12⟩ :=
    exists_lt_coord_of_sum_le_and_ne d₁ d₂ hLenEq (Nat.le_of_eq hSumEq) (.inr hDistinct)
  obtain ⟨r', hr2', hr1', hLt21⟩ :=
    exists_lt_coord_of_sum_le_and_ne d₂ d₁ hLenEq.symm (Nat.le_of_eq hSumEq.symm) (.inr hDistinct.symm)
  exact ⟨⟨r, hr1, hr2, hLt12, hBound₂ _ (List.getElem_mem hr2)⟩,
         ⟨r', hr2', hr1', hLt21, hBound₁ _ (List.getElem_mem hr1')⟩⟩

/-- Constructive coordinate finder returning the first index `r` where `d₂[r] < d₁[r]` (`0 Classical`). -/
def findBackwardCoord : List Nat → List Nat → Option Nat
  | x :: xs, y :: ys =>
    if y < x then some 0 else (findBackwardCoord xs ys).map (· + 1)
  | _, _ => none

theorem findBackwardCoord_complete :
    ∀ {d₁ d₂ : List Nat},
      (∃ (r : Nat) (hr₂ : r < d₂.length) (hr₁ : r < d₁.length), d₂[r]'hr₂ < d₁[r]'hr₁) →
      ∃ (r : Nat) (hr₂ : r < d₂.length) (hr₁ : r < d₁.length),
        findBackwardCoord d₁ d₂ = some r ∧ d₂[r]'hr₂ < d₁[r]'hr₁
  | [], _, ⟨_, _, hr₁, _⟩ => by cases hr₁
  | _, [], ⟨_, hr₂, _, _⟩ => by cases hr₂
  | x :: xs, y :: ys, hex => by
    simp only [findBackwardCoord]
    if hyx : y < x then
      exact ⟨0, Nat.zero_lt_succ _, Nat.zero_lt_succ _, by simp [hyx], hyx⟩
    else
      simp only [hyx, ↓reduceIte]
      have hexTail : ∃ (r : Nat) (hr₂ : r < ys.length) (hr₁ : r < xs.length), ys[r]'hr₂ < xs[r]'hr₁ := by
        obtain ⟨r, hr₂, hr₁, hlt⟩ := hex
        cases r with
        | zero => exact False.elim (hyx hlt)
        | succ r' => exact ⟨r', Nat.lt_of_succ_lt_succ hr₂, Nat.lt_of_succ_lt_succ hr₁, hlt⟩
      obtain ⟨r', hr₂', hr₁', hSome, hlt'⟩ := findBackwardCoord_complete hexTail
      exact ⟨r' + 1, Nat.succ_lt_succ hr₂', Nat.succ_lt_succ hr₁', by simp [hSome], hlt'⟩

/-- Unpack MSB-first digits without wrapping byte indices. Use the checked entry point for untrusted lengths. -/
def extractBaseWDigits (w ell1 : Nat) (digestBytes : List UInt8) : List Nat :=
  let wSafe := if w < 2 then 4 else w
  (List.range ell1).map fun idx =>
    if wSafe = 4 then
      let byteIdx := idx / 4
      let shift := (3 - (idx % 4)) * 2
      let b := (digestBytes.getD byteIdx 0).toNat
      (b / (2 ^ shift)) % 4
    else
      let lgW := Nat.log2 wSafe
      let perByte := 8 / lgW
      let byteIdx := idx / perByte
      let shift := (perByte - 1 - idx % perByte) * lgW
      ((digestBytes.getD byteIdx 0).toNat / 2 ^ shift) % wSafe

theorem extractBaseWDigits_bounds (w ell1 : Nat) (hw : 2 ≤ w) (digestBytes : List UInt8) :
    (extractBaseWDigits w ell1 digestBytes).length = ell1 ∧
    ∀ d ∈ extractBaseWDigits w ell1 digestBytes, d < w := by
  have hwNotLt : ¬ (w < 2) := by omega
  refine ⟨by simp [extractBaseWDigits], ?_⟩
  intro d hd
  simp only [extractBaseWDigits, hwNotLt, ↓reduceIte, List.mem_map] at hd
  obtain ⟨_, _, rfl⟩ := hd
  by_cases hw4 : w = 4
  · subst hw4; simp only [↓reduceIte]; exact Nat.mod_lt _ (by decide)
  · simp only [hw4, ↓reduceIte]; exact Nat.mod_lt _ (by omega)

/-- Validates power-of-two radix and the actual byte accesses before unpacking. -/
def extractBaseWDigitsChecked (w ell1 : Nat) (bytes : List UInt8) : Option (List Nat) :=
  if 2 ≤ w ∧ w ≤ 256 ∧ 2 ^ Nat.log2 w = w ∧
      ell1 ≤ bytes.length * (8 / Nat.log2 w) then
    some (extractBaseWDigits w ell1 bytes)
  else none

theorem extractBaseWDigitsChecked_eq (w ell1 : Nat) (bytes : List UInt8) :
    extractBaseWDigitsChecked w ell1 bytes =
      if 2 ≤ w ∧ w ≤ 256 ∧ 2 ^ Nat.log2 w = w ∧ ell1 ≤ bytes.length * (8 / Nat.log2 w) then
        some (extractBaseWDigits w ell1 bytes)
      else none := by rfl

theorem base16_msb_digits : extractBaseWDigitsChecked 16 4 [0xAB, 0xCD] = some [10, 11, 12, 13] := by
  decide +kernel

theorem base16_short_input_rejected : extractBaseWDigitsChecked 16 3 [0xAB] = none := by
  decide +kernel

/-- Regression: the high nibble is part of the message encoding. -/
theorem base16_high_nibble_not_discarded :
    extractBaseWDigitsChecked 16 2 [0xAB] ≠ extractBaseWDigitsChecked 16 2 [0xCB] := by
  decide +kernel

/-- Regression: base-four digits preserve the leading two bits. -/
theorem base4_high_crumb_not_discarded :
    extractBaseWDigitsChecked 4 4 [0xAB] ≠ extractBaseWDigitsChecked 4 4 [0xEB] := by
  decide +kernel

/-- Deterministic local CPU `TSW` counter grinder (`0` MPC gates), binding `kpIdx` in `thHashMsg`. -/
def grindTswCounterAux (suite : TweakableHashSuite) (w ell1 target : Nat)
    (rRand pkSeed pkRoot mu : List UInt8) (layerIdx : UInt32) (treeIdx : UInt64) (kpIdx : UInt32)
    (curCtr : Nat) : Nat → Option (Nat × List Nat × List UInt8)
  | 0 => none
  | fuel + 1 =>
    let hmsg := thHashMsg suite rRand pkSeed pkRoot mu layerIdx treeIdx kpIdx curCtr
    let digits := extractBaseWDigits w ell1 hmsg
    if checkTargetSum w ell1 target digits then
      some (curCtr, digits, hmsg)
    else
      grindTswCounterAux suite w ell1 target rRand pkSeed pkRoot mu layerIdx treeIdx kpIdx (curCtr + 1) fuel

theorem grindTswCounterAux_zero (suite : TweakableHashSuite) (w ell1 target : Nat)
    (rRand pkSeed pkRoot mu : List UInt8) (layerIdx : UInt32) (treeIdx : UInt64) (kpIdx : UInt32)
    (curCtr : Nat) :
    grindTswCounterAux suite w ell1 target rRand pkSeed pkRoot mu layerIdx treeIdx kpIdx curCtr 0 =
      none := by rfl

theorem grindTswCounterAux_succ (suite : TweakableHashSuite) (w ell1 target : Nat)
    (rRand pkSeed pkRoot mu : List UInt8) (layerIdx : UInt32) (treeIdx : UInt64) (kpIdx : UInt32)
    (curCtr fuel : Nat) :
    grindTswCounterAux suite w ell1 target rRand pkSeed pkRoot mu layerIdx treeIdx kpIdx curCtr
        (fuel + 1) =
      if checkTargetSum w ell1 target
          (extractBaseWDigits w ell1
            (thHashMsg suite rRand pkSeed pkRoot mu layerIdx treeIdx kpIdx curCtr)) then
        some (curCtr,
          extractBaseWDigits w ell1
            (thHashMsg suite rRand pkSeed pkRoot mu layerIdx treeIdx kpIdx curCtr),
          thHashMsg suite rRand pkSeed pkRoot mu layerIdx treeIdx kpIdx curCtr)
      else
        grindTswCounterAux suite w ell1 target rRand pkSeed pkRoot mu layerIdx treeIdx kpIdx
          (curCtr + 1) fuel := by rfl

theorem grindTswCounterAux_sound {suite : TweakableHashSuite} {w ell1 target : Nat}
    {rRand pkSeed pkRoot mu : List UInt8} {layerIdx : UInt32} {treeIdx : UInt64} {kpIdx : UInt32}
    {curCtr fuel ctr : Nat} {digits : List Nat} {hmsg : List UInt8}
    (h : grindTswCounterAux suite w ell1 target rRand pkSeed pkRoot mu layerIdx treeIdx kpIdx curCtr fuel =
          some (ctr, digits, hmsg)) :
    hmsg = thHashMsg suite rRand pkSeed pkRoot mu layerIdx treeIdx kpIdx ctr ∧
    digits = extractBaseWDigits w ell1 hmsg ∧
    checkTargetSum w ell1 target digits = true := by
  induction fuel generalizing curCtr with
  | zero => cases h
  | succ fuel ih =>
    simp only [grindTswCounterAux] at h
    let hm := thHashMsg suite rRand pkSeed pkRoot mu layerIdx treeIdx kpIdx curCtr
    let dg := extractBaseWDigits w ell1 hm
    cases hChk : checkTargetSum w ell1 target dg
    · rw [show checkTargetSum w ell1 target (extractBaseWDigits w ell1 (thHashMsg suite rRand pkSeed pkRoot mu layerIdx treeIdx kpIdx curCtr)) = false from hChk] at h
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      exact ih h
    · rw [show checkTargetSum w ell1 target (extractBaseWDigits w ell1 (thHashMsg suite rRand pkSeed pkRoot mu layerIdx treeIdx kpIdx curCtr)) = true from hChk] at h
      simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl, rfl⟩
      exact ⟨rfl, rfl, hChk⟩

/-! ## 4. WOTS+C Chains, FORS, XMSS, `Corduroy` / `Baggy` / `Jorts` & EUF-CMA -/

/-- Unified parameter set covering `Corduroy-Custody-128`, `Baggy-128f`, and stateful `Jorts`. -/
structure PqHashParams where
  w               : Nat
  ell1            : Nat
  subtreeHeight   : Nat
  numLayers       : Nat
  forsTrees       : Nat
  forsHeight      : Nat
  maxSigsLog2     : Nat
  statefulJorts : Bool
  deriving DecidableEq, Repr

def PqHashParams.targetSum (p : PqHashParams) : Nat := canonicalTargetSum p.w p.ell1

/-- Permissive model validity predicate supporting both full-width 256-bit presets and
    small-`ell1` fast algebraic test profiles (`compactTestParams`, `sbox7Params`, `zeroToyParams`).
    Production signers and verifiers enforce `PqHashParams.productionWellFormed`. -/
def PqHashParams.wellFormed (p : PqHashParams) : Bool :=
  decide (0 < p.numLayers) && decide (2 ≤ p.w) && decide (p.w ≤ 256) &&
  decide (0 < p.ell1) && decide (p.ell1 ≤ 256) &&
  decide (p.subtreeHeight ≤ 30) && decide (p.forsHeight ≤ 30) &&
  decide ((p.numLayers - 1) * p.subtreeHeight ≤ 64) &&
  decide (p.numLayers * p.subtreeHeight ≤ 62) &&
  (p.statefulJorts || (decide (0 < p.forsTrees) && decide (88 + p.forsTrees * p.forsHeight ≤ 512)))

/-- Exact production parameter validity predicate matching `PqHashParams::is_well_formed`
    in `crates/qsag-core/src/tsw_baggy.rs`: requires power-of-two `w ∈ [2, 256]`, exact 256-bit
    WOTS+C digest coverage (`ell1 * log2 w = 256`), `0 < subtreeHeight ≤ 30`, `forsHeight ≤ 30`,
    `0 < numLayers * subtreeHeight ≤ 62`, `0 < maxSigsLog2 ≤ numLayers * subtreeHeight`, and
    mode-exact FORS presence (`forsTrees = 0 ∧ forsHeight = 0` iff `statefulJorts`). -/
def PqHashParams.productionWellFormed (p : PqHashParams) : Bool :=
  decide (0 < p.numLayers) &&
  decide (2 ≤ p.w) && decide (p.w ≤ 256) && decide (2 ^ Nat.log2 p.w = p.w) &&
  decide (p.ell1 * Nat.log2 p.w = 256) &&
  decide (0 < p.subtreeHeight) && decide (p.subtreeHeight ≤ 30) &&
  decide (p.forsHeight ≤ 30) &&
  decide (0 < p.numLayers * p.subtreeHeight) &&
  decide (p.numLayers * p.subtreeHeight ≤ 62) &&
  decide (0 < p.maxSigsLog2) &&
  decide (p.maxSigsLog2 ≤ p.numLayers * p.subtreeHeight) &&
  (if p.statefulJorts then decide (p.forsTrees = 0) && decide (p.forsHeight = 0)
   else decide (0 < p.forsTrees) && decide (0 < p.forsHeight))

/-- Exact leaf/epoch range check matching `PqHashParams::leaf_idx_in_range` in `tsw_baggy.rs`:
    enforces `numLayers * subtreeHeight` in stateless mode and `min(maxSigsLog2, totalBits)` in stateful mode. -/
def PqHashParams.productionLeafIdxInRange (p : PqHashParams) (leafGlobalIdx : Nat) : Bool :=
  let totalBits := p.numLayers * p.subtreeHeight
  let capBits := if p.statefulJorts && decide (p.maxSigsLog2 < totalBits) then p.maxSigsLog2 else totalBits
  decide (leafGlobalIdx < 2 ^ capBits)

/-- Canonical wire byte length of a `PqHashSig` (`PQ_WIRE_MAGIC` + body): the value of
    `PqHashParams::wire_sig_bytes_checked` in `tsw_baggy.rs` whenever that does not overflow
    `usize` (where Rust's `wire_sig_bytes` returns `0`). -/
def PqHashParams.wireSigBytes (p : PqHashParams) : Nat :=
  let forsBytes := if p.statefulJorts then 0 else p.forsTrees * (32 + p.forsHeight * 32)
  49 + forsBytes + p.numLayers * (4 + p.ell1 * 32 + p.subtreeHeight * 32)

/-- Production presets matching `crates/qsag-core/src/tsw_baggy.rs` field-for-field. -/
def corduroyCustody128Params : PqHashParams := ⟨4, 128, 4, 7, 33, 6, 12, false⟩
def baggy128fParams          : PqHashParams := ⟨4, 128, 2, 16, 33, 6, 16, false⟩
def jortsPoseidon2Params     : PqHashParams := ⟨4, 128, 16, 1, 0, 0, 16, true⟩
def jortsBenchCachedParams   : PqHashParams := ⟨4, 128, 8, 1, 0, 0, 8, true⟩
def compactGoldenParams      : PqHashParams := ⟨16, 64, 2, 10, 24, 4, 4, false⟩
def compactJortsProdParams   : PqHashParams := ⟨16, 64, 2, 1, 0, 0, 2, true⟩

def compactJortsParams       : PqHashParams := ⟨4, 8, 2, 1, 0, 0, 2, true⟩

theorem corduroyCustody128Params_eq :
    corduroyCustody128Params = ⟨4, 128, 4, 7, 33, 6, 12, false⟩ := by rfl
theorem baggy128fParams_eq : baggy128fParams = ⟨4, 128, 2, 16, 33, 6, 16, false⟩ := by rfl
theorem jortsPoseidon2Params_eq : jortsPoseidon2Params = ⟨4, 128, 16, 1, 0, 0, 16, true⟩ := by rfl
theorem jortsBenchCachedParams_eq :
    jortsBenchCachedParams = ⟨4, 128, 8, 1, 0, 0, 8, true⟩ := by rfl
theorem compactGoldenParams_eq : compactGoldenParams = ⟨16, 64, 2, 10, 24, 4, 4, false⟩ := by rfl
theorem compactJortsProdParams_eq :
    compactJortsProdParams = ⟨16, 64, 2, 1, 0, 0, 2, true⟩ := by rfl
theorem compactJortsParams_eq : compactJortsParams = ⟨4, 8, 2, 1, 0, 0, 2, true⟩ := by rfl

/-- Secret key `(skSeed, skPrf, pkSeed)`. -/
structure PqSecretKey where
  skSeed : List UInt8
  skPrf  : List UInt8
  pkSeed : List UInt8
  deriving DecidableEq, Repr

/-- Public key `(pkSeed, pkRoot)` (`64` bytes canonical encoding: `32 B || 32 B`). -/
structure PqPublicKey where
  pkSeed : List UInt8
  pkRoot : List UInt8
  deriving DecidableEq, Repr

/-- Advance a WOTS+C chain `steps` iterations starting from `startStep`. -/
def wotsChainSteps (suite : TweakableHashSuite) (pkSeed : List UInt8)
    (layer : UInt32) (tree : UInt64) (kp chain startStep : Nat) : Nat → List UInt8 → List UInt8
  | 0, cur => cur
  | k + 1, cur =>
    let adrs : HashAdrs := ⟨layer, tree, .wotsHash, UInt32.ofNat kp, UInt32.ofNat chain, UInt32.ofNat startStep⟩
    let nextVal := thChainF suite pkSeed adrs cur
    wotsChainSteps suite pkSeed layer tree kp chain (startStep + 1) k nextVal

theorem wotsChainSteps_add (suite : TweakableHashSuite) (pkSeed : List UInt8)
    (layer : UInt32) (tree : UInt64) (kp chain : Nat) :
    ∀ (a b startStep : Nat) (cur : List UInt8),
      wotsChainSteps suite pkSeed layer tree kp chain (startStep + a) b
        (wotsChainSteps suite pkSeed layer tree kp chain startStep a cur) =
      wotsChainSteps suite pkSeed layer tree kp chain startStep (a + b) cur
  | 0, b, startStep, cur => by simp [wotsChainSteps]
  | a + 1, b, startStep, cur => by
    rw [Nat.succ_add]
    simp only [wotsChainSteps]
    have hShift : startStep + (a + 1) = (startStep + 1) + a := by omega
    rw [hShift, wotsChainSteps_add suite pkSeed layer tree kp chain a b (startStep + 1)]

def wotsSecretBase (suite : TweakableHashSuite) (sk : PqSecretKey)
    (layer : UInt32) (tree : UInt64) (kp chain : Nat) : List UInt8 :=
  thSecretPrf suite sk.pkSeed sk.skSeed
    ⟨layer, tree, .wotsPrf, UInt32.ofNat kp, UInt32.ofNat chain, 0⟩

theorem wotsSecretBase_eq (suite : TweakableHashSuite) (sk : PqSecretKey)
    (layer : UInt32) (tree : UInt64) (kp chain : Nat) :
    wotsSecretBase suite sk layer tree kp chain =
      thSecretPrf suite sk.pkSeed sk.skSeed
        ⟨layer, tree, .wotsPrf, UInt32.ofNat kp, UInt32.ofNat chain, 0⟩ := by rfl

theorem wotsChainSteps_zero (suite : TweakableHashSuite) (pkSeed : List UInt8)
    (layer : UInt32) (tree : UInt64) (kp chain startStep : Nat) (cur : List UInt8) :
    wotsChainSteps suite pkSeed layer tree kp chain startStep 0 cur = cur := by rfl

theorem wotsChainSteps_succ (suite : TweakableHashSuite) (pkSeed : List UInt8)
    (layer : UInt32) (tree : UInt64) (kp chain startStep k : Nat) (cur : List UInt8) :
    wotsChainSteps suite pkSeed layer tree kp chain startStep (k + 1) cur =
      let adrs : HashAdrs := ⟨layer, tree, .wotsHash, UInt32.ofNat kp, UInt32.ofNat chain, UInt32.ofNat startStep⟩
      wotsChainSteps suite pkSeed layer tree kp chain (startStep + 1) k (thChainF suite pkSeed adrs cur) := by rfl

def computeWotsEndpoints (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey)
    (layer : UInt32) (tree : UInt64) (kp : Nat) : List (List UInt8) :=
  (List.range params.ell1).map fun r =>
    wotsChainSteps suite sk.pkSeed layer tree kp r 0 (params.w - 1)
      (wotsSecretBase suite sk layer tree kp r)

def computeWotsPk (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey)
    (layer : UInt32) (tree : UInt64) (kp : Nat) : List UInt8 :=
  thTweakTl suite sk.pkSeed ⟨layer, tree, .wotsPk, UInt32.ofNat kp, 0, 0⟩
    (computeWotsEndpoints suite params sk layer tree kp)

theorem computeWotsEndpoints_eq (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey)
    (layer : UInt32) (tree : UInt64) (kp : Nat) :
    computeWotsEndpoints suite params sk layer tree kp =
      (List.range params.ell1).map (fun r => wotsChainSteps suite sk.pkSeed layer tree kp r 0 (params.w - 1)
        (wotsSecretBase suite sk layer tree kp r)) := by rfl

theorem computeWotsPk_eq (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey)
    (layer : UInt32) (tree : UInt64) (kp : Nat) :
    computeWotsPk suite params sk layer tree kp =
      thTweakTl suite sk.pkSeed ⟨layer, tree, .wotsPk, UInt32.ofNat kp, 0, 0⟩
        ((List.range params.ell1).map fun r =>
          wotsChainSteps suite sk.pkSeed layer tree kp r 0 (params.w - 1)
            (wotsSecretBase suite sk layer tree kp r)) := by rfl

def recoverWotsEndpoints (suite : TweakableHashSuite) (params : PqHashParams) (pkSeed : List UInt8)
    (layer : UInt32) (tree : UInt64) (kp : Nat)
    (digits : List Nat) (sigChains : List (List UInt8)) : List (List UInt8) :=
  (List.range params.ell1).map fun r =>
    let dr := digits.getD r 0
    let sigVal := sigChains.getD r []
    wotsChainSteps suite pkSeed layer tree kp r dr ((params.w - 1) - dr) sigVal

def recoverWotsPkFromSig (suite : TweakableHashSuite) (params : PqHashParams) (pkSeed : List UInt8)
    (layer : UInt32) (tree : UInt64) (kp : Nat)
    (digits : List Nat) (sigChains : List (List UInt8)) : List UInt8 :=
  thTweakTl suite pkSeed ⟨layer, tree, .wotsPk, UInt32.ofNat kp, 0, 0⟩
    (recoverWotsEndpoints suite params pkSeed layer tree kp digits sigChains)

theorem list_getD_map_range {α : Type} (n : Nat) (f : Nat → α) (dflt : α) {i : Nat} (hi : i < n) :
    ((List.range n).map f).getD i dflt = f i := by
  have hi' : i < ((List.range n).map f).length := by simpa using hi
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']
  simp

theorem list_getD_eq_getElem {α : Type} (xs : List α) (dflt : α) {i : Nat} (hi : i < xs.length) :
    xs.getD i dflt = xs[i]'hi := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  rfl

theorem recoverWotsPkFromSig_eq_computeWotsPk
    (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey)
    (layer : UInt32) (tree : UInt64) (kp : Nat) (digits : List Nat)
    (hValid : checkTargetSum params.w params.ell1 params.targetSum digits = true) :
    let sigChains := (List.range params.ell1).map fun r =>
      let dr := digits.getD r 0
      wotsChainSteps suite sk.pkSeed layer tree kp r 0 dr (wotsSecretBase suite sk layer tree kp r)
    recoverWotsPkFromSig suite params sk.pkSeed layer tree kp digits sigChains =
      computeWotsPk suite params sk layer tree kp := by
  intro sigChains
  obtain ⟨hLen, hBound, _⟩ := (checkTargetSum_iff params.w params.ell1 params.targetSum digits).mp hValid
  unfold recoverWotsPkFromSig computeWotsPk recoverWotsEndpoints computeWotsEndpoints
  congr 1
  apply List.map_congr_left
  intro r hrMem
  have hrLt : r < params.ell1 := List.mem_range.mp hrMem
  have hSigGet : sigChains.getD r [] =
      wotsChainSteps suite sk.pkSeed layer tree kp r 0 (digits.getD r 0) (wotsSecretBase suite sk layer tree kp r) :=
    list_getD_map_range params.ell1 _ [] hrLt
  rw [hSigGet]
  have hdrLt : digits.getD r 0 < params.w := by
    have hrDigits : r < digits.length := hLen ▸ hrLt
    rw [list_getD_eq_getElem digits 0 hrDigits]
    exact hBound _ (List.getElem_mem hrDigits)
  have hStepEq := wotsChainSteps_add suite sk.pkSeed layer tree kp r
    (digits.getD r 0) ((params.w - 1) - digits.getD r 0) 0 (wotsSecretBase suite sk layer tree kp r)
  simp only [Nat.zero_add] at hStepEq
  have hSumW : digits.getD r 0 + ((params.w - 1) - digits.getD r 0) = params.w - 1 := by omega
  rw [hStepEq, hSumW]

/-! ### Parametric Binary Merkle Subtree + Auth Path (`FORS` & `XMSS` Unified) -/

def computeMerkleNode (suite : TweakableHashSuite) (pkSeed : List UInt8)
    (layer : UInt32) (tree : UInt64) (nodeKind : AdrsKind)
    (leafFn : Nat → List UInt8) : Nat → Nat → List UInt8
  | 0, nodeIdx => leafFn nodeIdx
  | h + 1, nodeIdx =>
    let left  := computeMerkleNode suite pkSeed layer tree nodeKind leafFn h (2 * nodeIdx)
    let right := computeMerkleNode suite pkSeed layer tree nodeKind leafFn h (2 * nodeIdx + 1)
    let adrs : HashAdrs := ⟨layer, tree, nodeKind, 0, UInt32.ofNat (h + 1), UInt32.ofNat nodeIdx⟩
    thNodeH suite pkSeed adrs left right

def buildMerkleAuthPath (suite : TweakableHashSuite) (pkSeed : List UInt8)
    (layer : UInt32) (tree : UInt64) (nodeKind : AdrsKind)
    (leafFn : Nat → List UInt8) : Nat → Nat → Nat → List (List UInt8)
  | 0, _, _ => []
  | h + 1, nodeIdx, localIdx =>
    let half := 2 ^ h
    if localIdx < half then
      let sib := computeMerkleNode suite pkSeed layer tree nodeKind leafFn h (2 * nodeIdx + 1)
      sib :: buildMerkleAuthPath suite pkSeed layer tree nodeKind leafFn h (2 * nodeIdx) localIdx
    else
      let sib := computeMerkleNode suite pkSeed layer tree nodeKind leafFn h (2 * nodeIdx)
      sib :: buildMerkleAuthPath suite pkSeed layer tree nodeKind leafFn h (2 * nodeIdx + 1) (localIdx - half)

theorem computeMerkleNode_zero (suite : TweakableHashSuite) (pkSeed : List UInt8)
    (layer : UInt32) (tree : UInt64) (nodeKind : AdrsKind) (leafFn : Nat → List UInt8) (nodeIdx : Nat) :
    computeMerkleNode suite pkSeed layer tree nodeKind leafFn 0 nodeIdx = leafFn nodeIdx := by rfl

theorem computeMerkleNode_succ (suite : TweakableHashSuite) (pkSeed : List UInt8)
    (layer : UInt32) (tree : UInt64) (nodeKind : AdrsKind) (leafFn : Nat → List UInt8) (h nodeIdx : Nat) :
    computeMerkleNode suite pkSeed layer tree nodeKind leafFn (h + 1) nodeIdx =
      let left  := computeMerkleNode suite pkSeed layer tree nodeKind leafFn h (2 * nodeIdx)
      let right := computeMerkleNode suite pkSeed layer tree nodeKind leafFn h (2 * nodeIdx + 1)
      let adrs : HashAdrs := ⟨layer, tree, nodeKind, 0, UInt32.ofNat (h + 1), UInt32.ofNat nodeIdx⟩
      thNodeH suite pkSeed adrs left right := by rfl

theorem buildMerkleAuthPath_zero (suite : TweakableHashSuite) (pkSeed : List UInt8)
    (layer : UInt32) (tree : UInt64) (nodeKind : AdrsKind) (leafFn : Nat → List UInt8) (nodeIdx localIdx : Nat) :
    buildMerkleAuthPath suite pkSeed layer tree nodeKind leafFn 0 nodeIdx localIdx = [] := by rfl

theorem buildMerkleAuthPath_succ (suite : TweakableHashSuite) (pkSeed : List UInt8)
    (layer : UInt32) (tree : UInt64) (nodeKind : AdrsKind) (leafFn : Nat → List UInt8) (h nodeIdx localIdx : Nat) :
    buildMerkleAuthPath suite pkSeed layer tree nodeKind leafFn (h + 1) nodeIdx localIdx =
      if localIdx < 2 ^ h then
        computeMerkleNode suite pkSeed layer tree nodeKind leafFn h (2 * nodeIdx + 1) ::
          buildMerkleAuthPath suite pkSeed layer tree nodeKind leafFn h (2 * nodeIdx) localIdx
      else
        computeMerkleNode suite pkSeed layer tree nodeKind leafFn h (2 * nodeIdx) ::
          buildMerkleAuthPath suite pkSeed layer tree nodeKind leafFn h (2 * nodeIdx + 1) (localIdx - 2 ^ h) := by rfl

@[expose] def walkMerkleAuthPath (suite : TweakableHashSuite) (pkSeed : List UInt8)
    (layer : UInt32) (tree : UInt64) (nodeKind : AdrsKind) :
    Nat → Nat → Nat → List UInt8 → List (List UInt8) → Option (List UInt8)
  | 0, _, _, leafHash, [] => some leafHash
  | 0, _, _, _, _ :: _ => none
  | _ + 1, _, _, _, [] => none
  | h + 1, nodeIdx, localIdx, leafHash, sib :: rest =>
    let half := 2 ^ h
    let adrs : HashAdrs := ⟨layer, tree, nodeKind, 0, UInt32.ofNat (h + 1), UInt32.ofNat nodeIdx⟩
    if localIdx < half then
      match walkMerkleAuthPath suite pkSeed layer tree nodeKind h (2 * nodeIdx) localIdx leafHash rest with
      | none => none
      | some sub => some (thNodeH suite pkSeed adrs sub sib)
    else
      match walkMerkleAuthPath suite pkSeed layer tree nodeKind h (2 * nodeIdx + 1) (localIdx - half) leafHash rest with
      | none => none
      | some sub => some (thNodeH suite pkSeed adrs sib sub)

theorem walkMerkleAuthPath_buildMerkleAuthPath
    (suite : TweakableHashSuite) (pkSeed : List UInt8)
    (layer : UInt32) (tree : UInt64) (nodeKind : AdrsKind) (leafFn : Nat → List UInt8) :
    ∀ (h nodeIdx localIdx : Nat), localIdx < 2 ^ h →
      walkMerkleAuthPath suite pkSeed layer tree nodeKind h nodeIdx localIdx
        (leafFn (nodeIdx * (2 ^ h) + localIdx))
        (buildMerkleAuthPath suite pkSeed layer tree nodeKind leafFn h nodeIdx localIdx) =
      some (computeMerkleNode suite pkSeed layer tree nodeKind leafFn h nodeIdx)
  | 0, nodeIdx, localIdx, hLt => by
    have h0 : localIdx = 0 := by simp at hLt; exact hLt
    subst h0
    simp [buildMerkleAuthPath, walkMerkleAuthPath, computeMerkleNode]
  | h + 1, nodeIdx, localIdx, hLt => by
    simp only [buildMerkleAuthPath]
    have hMul : nodeIdx * (2 ^ (h + 1)) = (2 * nodeIdx) * (2 ^ h) := by
      rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm (nodeIdx * 2 ^ h) 2, Nat.mul_assoc]
    by_cases hHalf : localIdx < 2 ^ h
    · simp only [hHalf, ↓reduceIte, walkMerkleAuthPath]
      have hIdxEq : nodeIdx * (2 ^ (h + 1)) + localIdx = (2 * nodeIdx) * (2 ^ h) + localIdx := by rw [hMul]
      rw [hIdxEq, walkMerkleAuthPath_buildMerkleAuthPath suite pkSeed layer tree nodeKind leafFn h (2 * nodeIdx) localIdx hHalf]; rfl
    · simp only [hHalf, ↓reduceIte, walkMerkleAuthPath]
      have hSubLt : localIdx - 2 ^ h < 2 ^ h := by rw [Nat.pow_succ] at hLt; omega
      have hIdxEq : nodeIdx * (2 ^ (h + 1)) + localIdx = (2 * nodeIdx + 1) * (2 ^ h) + (localIdx - 2 ^ h) := by
        rw [hMul, Nat.add_mul, Nat.one_mul, Nat.add_assoc, Nat.add_sub_of_le (Nat.le_of_not_lt hHalf)]
      rw [hIdxEq, walkMerkleAuthPath_buildMerkleAuthPath suite pkSeed layer tree nodeKind leafFn h (2 * nodeIdx + 1) (localIdx - 2 ^ h) hSubLt]; rfl

/-- Constructive `0 Classical` collision extraction along a Merkle auth path when two distinct
    `(leafHash, authPath)` pairs at the same `(h, nodeIdx, localIdx)` produce the same root. -/
def walkMerkleAuthPath_collision_extract
    (suite : TweakableHashSuite) (pkSeed : List UInt8)
    (layer : UInt32) (tree : UInt64) (nodeKind : AdrsKind) :
    ∀ (h nodeIdx localIdx : Nat) {leaf1 leaf2 : List UInt8} {path1 path2 : List (List UInt8)} {root : List UInt8},
      (leaf1 ≠ leaf2 ∨ path1 ≠ path2) →
      walkMerkleAuthPath suite pkSeed layer tree nodeKind h nodeIdx localIdx leaf1 path1 = some root →
      walkMerkleAuthPath suite pkSeed layer tree nodeKind h nodeIdx localIdx leaf2 path2 = some root →
      HashCollisionWitness suite.rawHash
  | 0, _, _, leaf1, leaf2, [], [], _, hDiff, h1, h2 => by
    simp only [walkMerkleAuthPath, Option.some.injEq] at h1 h2
    have hLeafEq : leaf1 = leaf2 := h1.trans h2.symm
    exact False.elim (by rcases hDiff with hne | hpne; exact hne hLeafEq; exact hpne rfl)
  | 0, _, _, _, _, [], _ :: _, _, _, _, h2 => by simp [walkMerkleAuthPath] at h2
  | 0, _, _, _, _, _ :: _, _, _, _, h1, _ => by simp [walkMerkleAuthPath] at h1
  | _ + 1, _, _, _, _, [], _, _, _, h1, _ => by simp [walkMerkleAuthPath] at h1
  | _ + 1, _, _, _, _, _ :: _, [], _, _, _, h2 => by simp [walkMerkleAuthPath] at h2
  | h + 1, nodeIdx, localIdx, leaf1, leaf2, sib1 :: rest1, sib2 :: rest2, root, hDiff, h1, h2 =>
    let adrs : HashAdrs := ⟨layer, tree, nodeKind, 0, UInt32.ofNat (h + 1), UInt32.ofNat nodeIdx⟩
    if hHalf : localIdx < 2 ^ h then
      match hSub1 : walkMerkleAuthPath suite pkSeed layer tree nodeKind h (2 * nodeIdx) localIdx leaf1 rest1,
            hSub2 : walkMerkleAuthPath suite pkSeed layer tree nodeKind h (2 * nodeIdx) localIdx leaf2 rest2 with
      | none, _ => False.elim (by
          unfold walkMerkleAuthPath at h1
          simp only [hHalf, ↓reduceIte, hSub1] at h1
          cases h1)
      | _, none => False.elim (by
          unfold walkMerkleAuthPath at h2
          simp only [hHalf, ↓reduceIte, hSub2] at h2
          cases h2)
      | some sub1, some sub2 =>
        have hRootEq : thNodeH suite pkSeed adrs sub1 sib1 = thNodeH suite pkSeed adrs sub2 sib2 := by
          unfold walkMerkleAuthPath at h1 h2
          simp only [hHalf, ↓reduceIte, hSub1, hSub2, Option.some.injEq] at h1 h2
          exact h1.trans h2.symm
        if hInputsNe : sub1 ≠ sub2 ∨ sib1 ≠ sib2 then
          match thCall_binds_or_collision suite hRootEq with
          | .inl ⟨_, _, _, hArgsEq⟩ =>
            False.elim (by
              simp only [List.cons.injEq, and_true] at hArgsEq
              rcases hInputsNe with hs | hsib
              · exact hs hArgsEq.1
              · exact hsib hArgsEq.2)
          | .inr col => col
        else
          have hSubEq : sub1 = sub2 := Decidable.of_not_not (fun hn => hInputsNe (.inl hn))
          have hSibEq : sib1 = sib2 := Decidable.of_not_not (fun hn => hInputsNe (.inr hn))
          have hRestDiff : leaf1 ≠ leaf2 ∨ rest1 ≠ rest2 := by
            if hL : leaf1 = leaf2 then
              right
              intro hR
              rcases hDiff with hLne | hPne
              · exact hLne hL
              · exact hPne (by rw [hSibEq, hR])
            else
              exact .inl hL
          walkMerkleAuthPath_collision_extract suite pkSeed layer tree nodeKind h (2 * nodeIdx) localIdx
            hRestDiff hSub1 (hSubEq ▸ hSub2)
    else
      match hSub1 : walkMerkleAuthPath suite pkSeed layer tree nodeKind h (2 * nodeIdx + 1) (localIdx - 2 ^ h) leaf1 rest1,
            hSub2 : walkMerkleAuthPath suite pkSeed layer tree nodeKind h (2 * nodeIdx + 1) (localIdx - 2 ^ h) leaf2 rest2 with
      | none, _ => False.elim (by
          unfold walkMerkleAuthPath at h1
          simp only [hHalf, ↓reduceIte, hSub1] at h1
          cases h1)
      | _, none => False.elim (by
          unfold walkMerkleAuthPath at h2
          simp only [hHalf, ↓reduceIte, hSub2] at h2
          cases h2)
      | some sub1, some sub2 =>
        have hRootEq : thNodeH suite pkSeed adrs sib1 sub1 = thNodeH suite pkSeed adrs sib2 sub2 := by
          unfold walkMerkleAuthPath at h1 h2
          simp only [hHalf, ↓reduceIte, hSub1, hSub2, Option.some.injEq] at h1 h2
          exact h1.trans h2.symm
        if hInputsNe : sib1 ≠ sib2 ∨ sub1 ≠ sub2 then
          match thCall_binds_or_collision suite hRootEq with
          | .inl ⟨_, _, _, hArgsEq⟩ =>
            False.elim (by
              simp only [List.cons.injEq, and_true] at hArgsEq
              rcases hInputsNe with hsib | hs
              · exact hsib hArgsEq.1
              · exact hs hArgsEq.2)
          | .inr col => col
        else
          have hSibEq : sib1 = sib2 := Decidable.of_not_not (fun hn => hInputsNe (.inl hn))
          have hSubEq : sub1 = sub2 := Decidable.of_not_not (fun hn => hInputsNe (.inr hn))
          have hRestDiff : leaf1 ≠ leaf2 ∨ rest1 ≠ rest2 := by
            if hL : leaf1 = leaf2 then
              right
              intro hR
              rcases hDiff with hLne | hPne
              · exact hLne hL
              · exact hPne (by rw [hSibEq, hR])
            else
              exact .inl hL
          walkMerkleAuthPath_collision_extract suite pkSeed layer tree nodeKind h (2 * nodeIdx + 1) (localIdx - 2 ^ h)
            hRestDiff hSub1 (hSubEq ▸ hSub2)

/-- Legacy flattened FORS address used by the existing MPC interface; see the indexed production primitives below. -/
def forsSecretLeaf (suite : TweakableHashSuite) (sk : PqSecretKey)
    (treeIdx : UInt64) (kpIdx globalForsLeaf : Nat) : List UInt8 :=
  thSecretPrf suite sk.pkSeed sk.skSeed
    ⟨0, treeIdx, .forsPrf, UInt32.ofNat kpIdx, 0, UInt32.ofNat globalForsLeaf⟩

def forsLeafHashFromSecret (suite : TweakableHashSuite) (pkSeed : List UInt8)
    (treeIdx : UInt64) (kpIdx globalForsLeaf : Nat) (secVal : List UInt8) : List UInt8 :=
  thChainF suite pkSeed
    ⟨0, treeIdx, .forsTree, UInt32.ofNat kpIdx, 0, UInt32.ofNat globalForsLeaf⟩ secVal

def forsLeafFn (suite : TweakableHashSuite) (sk : PqSecretKey)
    (treeIdx : UInt64) (kpIdx : Nat) : Nat → List UInt8 :=
  fun globalU => forsLeafHashFromSecret suite sk.pkSeed treeIdx kpIdx globalU
    (forsSecretLeaf suite sk treeIdx kpIdx globalU)

/-- Production FORS secret address, with separate tree and leaf indices matching the Rust interface. -/
def forsIndexedSecretLeaf (suite : TweakableHashSuite) (sk : PqSecretKey)
    (tree : UInt64) (kp j u : Nat) : List UInt8 :=
  thSecretPrf suite sk.pkSeed sk.skSeed
    ⟨0, tree, .forsPrf, UInt32.ofNat kp, UInt32.ofNat j, UInt32.ofNat u⟩

def forsIndexedLeafHash (suite : TweakableHashSuite) (pkSeed : List UInt8)
    (tree : UInt64) (kp j u : Nat) (secret : List UInt8) : List UInt8 :=
  thChainF suite pkSeed
    ⟨0, tree, .forsTree, UInt32.ofNat kp, UInt32.ofNat j, UInt32.ofNat u⟩ secret

/-- Production-address regression: tree 1, leaf 2 at height 6 is encoded as `(1, 2)`. -/
theorem fors_leaf_address_split (suite : TweakableHashSuite) (pkSeed secret : List UInt8)
    (tree : UInt64) (kp : Nat) :
    forsIndexedLeafHash suite pkSeed tree kp 1 2 secret =
      thChainF suite pkSeed ⟨0, tree, .forsTree, UInt32.ofNat kp, 1, 2⟩ secret := by rfl

theorem fors_secret_address_split (suite : TweakableHashSuite) (sk : PqSecretKey)
    (tree : UInt64) (kp : Nat) :
    forsIndexedSecretLeaf suite sk tree kp 1 2 =
      thSecretPrf suite sk.pkSeed sk.skSeed ⟨0, tree, .forsPrf, UInt32.ofNat kp, 1, 2⟩ := by rfl

/-- The old flattened address cannot encode the same hash preimage as a nonzero tree index. -/
theorem fors_flattened_address_rejected (pkSeed secret : List UInt8) (tree : UInt64) (kp : Nat) :
    thPreimage tagThF pkSeed ⟨0, tree, .forsTree, UInt32.ofNat kp, 1, 2⟩ [secret] ≠
    thPreimage tagThF pkSeed ⟨0, tree, .forsTree, UInt32.ofNat kp, 0, 66⟩ [secret] := by
  intro h
  have ha := (thPreimage_injective h).2.2.1
  have hc := congrArg UInt32.toNat (congrArg HashAdrs.chainIdx ha)
  change 1 = 0 at hc
  omega

def computeXmssSubtreeRoot (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (layer : UInt32) (treeIdx : UInt64) : List UInt8 :=
  computeMerkleNode suite sk.pkSeed layer treeIdx .tree
    (computeWotsPk suite params sk layer treeIdx) params.subtreeHeight 0

theorem forsSecretLeaf_eq (suite : TweakableHashSuite) (sk : PqSecretKey)
    (treeIdx : UInt64) (kpIdx globalForsLeaf : Nat) :
    forsSecretLeaf suite sk treeIdx kpIdx globalForsLeaf =
      thSecretPrf suite sk.pkSeed sk.skSeed
        ⟨0, treeIdx, .forsPrf, UInt32.ofNat kpIdx, 0, UInt32.ofNat globalForsLeaf⟩ := by rfl

theorem forsLeafFn_eq (suite : TweakableHashSuite) (sk : PqSecretKey)
    (treeIdx : UInt64) (kpIdx globalU : Nat) :
    forsLeafFn suite sk treeIdx kpIdx globalU =
      thChainF suite sk.pkSeed
        ⟨0, treeIdx, .forsTree, UInt32.ofNat kpIdx, 0, UInt32.ofNat globalU⟩
        (forsSecretLeaf suite sk treeIdx kpIdx globalU) := by rfl

theorem forsIndexedSecretLeaf_eq (suite : TweakableHashSuite) (sk : PqSecretKey)
    (tree : UInt64) (kp j u : Nat) :
    forsIndexedSecretLeaf suite sk tree kp j u =
      thSecretPrf suite sk.pkSeed sk.skSeed
        ⟨0, tree, .forsPrf, UInt32.ofNat kp, UInt32.ofNat j, UInt32.ofNat u⟩ := by rfl

theorem forsIndexedLeafHash_eq (suite : TweakableHashSuite) (pkSeed : List UInt8)
    (tree : UInt64) (kp j u : Nat) (secret : List UInt8) :
    forsIndexedLeafHash suite pkSeed tree kp j u secret =
      thChainF suite pkSeed
        ⟨0, tree, .forsTree, UInt32.ofNat kp, UInt32.ofNat j, UInt32.ofNat u⟩ secret := by rfl

theorem computeXmssSubtreeRoot_eq (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (layer : UInt32) (treeIdx : UInt64) :
    computeXmssSubtreeRoot suite params sk layer treeIdx =
      computeMerkleNode suite sk.pkSeed layer treeIdx .tree
        (computeWotsPk suite params sk layer treeIdx) params.subtreeHeight 0 := by rfl

/-- Derive the canonical `PqPublicKey` `(pkSeed, pkRoot)` from top layer `d - 1`, `treeIdx = 0`. -/
@[expose] def derivePublicKey (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey) : PqPublicKey :=
  let topLayer := UInt32.ofNat (params.numLayers - 1)
  { pkSeed := sk.pkSeed
    pkRoot := computeXmssSubtreeRoot suite params sk topLayer 0 }

structure LayerXmssSig where
  tswCtr     : Nat
  wotsChains : List (List UInt8)
  authPath   : List (List UInt8)
  deriving DecidableEq, Repr

structure ForsTreeOpening where
  secretVal : List UInt8
  authPath  : List (List UInt8)
  deriving DecidableEq, Repr

structure PqHashSig where
  rRand         : List UInt8
  msgTswCtr     : Nat
  leafGlobalIdx : Nat
  forsOpenings  : List ForsTreeOpening
  layerSigs     : List LayerXmssSig
  deriving DecidableEq, Repr

def extractBitWindow (bytes : List UInt8) (startBit width : Nat) : Nat :=
  ((List.range width).foldl (fun acc b =>
    let pos := startBit + b
    let byteVal := (bytes.getD (pos / 8) 0).toNat
    acc * 2 + (byteVal >>> (7 - pos % 8)) % 2) 0) % (2 ^ width)

/-- Checked wire bit window; zero-width windows require no byte access. -/
def extractBitWindowChecked (bytes : List UInt8) (startBit width : Nat) : Option Nat :=
  if width ≤ 64 ∧ (width = 0 ∨ startBit + width ≤ bytes.length * 8) then
    some (extractBitWindow bytes startBit width)
  else none

theorem bit_window_msb_first : extractBitWindowChecked [0x80] 0 1 = some 1 := by
  decide +kernel

theorem bit_window_out_of_bounds_rejected : extractBitWindowChecked [0x80] 8 1 = none := by
  decide +kernel

def deriveForsIndices (k a : Nat) (hmsg : List UInt8) : List Nat :=
  (List.range k).map fun j => extractBitWindow hmsg (88 + j * a) a

theorem deriveForsIndices_bounds (k a : Nat) (hmsg : List UInt8) :
    (deriveForsIndices k a hmsg).length = k ∧
    ∀ idx ∈ deriveForsIndices k a hmsg, idx < 2 ^ a := by
  refine ⟨by simp [deriveForsIndices], ?_⟩
  intro idx hMem
  simp only [deriveForsIndices, List.mem_map] at hMem
  obtain ⟨_, _, rfl⟩ := hMem
  exact Nat.mod_lt _ (Nat.two_pow_pos a)

def recoverForsTreeRoots (suite : TweakableHashSuite) (params : PqHashParams)
    (pkSeed : List UInt8) (treeIdx : UInt64) (kpIdx : Nat)
    (idxs : List Nat) (openings : List ForsTreeOpening) (j : Nat) : Nat → Option (List (List UInt8))
  | 0 => some []
  | rem + 1 =>
    let idxJ := idxs.getD j 0
    let op := openings.getD j ⟨[], []⟩
    let globalU := j * (2 ^ params.forsHeight) + idxJ
    let leafH := forsLeafHashFromSecret suite pkSeed treeIdx kpIdx globalU op.secretVal
    match walkMerkleAuthPath suite pkSeed 0 treeIdx .forsTree params.forsHeight j idxJ leafH op.authPath with
    | none => none
    | some rJ =>
      match recoverForsTreeRoots suite params pkSeed treeIdx kpIdx idxs openings (j + 1) rem with
      | none => none
      | some rs => some (rJ :: rs)

def recoverForsPk (suite : TweakableHashSuite) (params : PqHashParams)
    (pkSeed : List UInt8) (treeIdx : UInt64) (kpIdx : Nat)
    (hmsg : List UInt8) (openings : List ForsTreeOpening) : Option (List UInt8) :=
  if openings.length ≠ params.forsTrees then none
  else
    let idxs := deriveForsIndices params.forsTrees params.forsHeight hmsg
    match recoverForsTreeRoots suite params pkSeed treeIdx kpIdx idxs openings 0 params.forsTrees with
    | none => none
    | some roots =>
      some (thTweakTl suite pkSeed ⟨0, treeIdx, .forsRoots, UInt32.ofNat kpIdx, 0, 0⟩ roots)

def deriveStatelessLeafIdx (params : PqHashParams) (hmsg0 : List UInt8) : Nat :=
  extractBitWindow hmsg0 0 (params.numLayers * params.subtreeHeight)

theorem deriveStatelessLeafIdx_lt (params : PqHashParams) (hmsg0 : List UInt8) :
    deriveStatelessLeafIdx params hmsg0 < 2 ^ (params.numLayers * params.subtreeHeight) :=
  Nat.mod_lt _ (Nat.two_pow_pos _)

/-- Production stateless input derivation. FORS consumes the first byte-rounded window;
    the hypertree leaf starts in the following byte, rather than sharing the fixed legacy offset.
    The leaf component is consumed by `evalStatelessCheckedSign` / `verifyStatelessChecked`;
    the FORS index component is not yet consumed by any signer or verifier. -/
def deriveStatelessInputs (suite : TweakableHashSuite) (params : PqHashParams)
    (rRand pkSeed pkRoot mu : List UInt8) : Option (Nat × List Nat) :=
  if !params.wellFormed || params.statefulJorts then none
  else
    let forsBytes := (params.forsTrees * params.forsHeight + 7) / 8
    let treeBits := params.numLayers * params.subtreeHeight
    let treeBytes := (treeBits + 7) / 8
    let digest := thXofMsg suite rRand pkSeed pkRoot mu (forsBytes + treeBytes)
    let forsSlice := digest.take forsBytes
    let treeSlice := digest.drop forsBytes
    some (extractBitWindow treeSlice 0 treeBits,
      (List.range params.forsTrees).map (fun j => extractBitWindow forsSlice (j * params.forsHeight) params.forsHeight))

theorem deriveStatelessInputs_leaf_bound (suite : TweakableHashSuite) (params : PqHashParams)
    (rRand pkSeed pkRoot mu : List UInt8) (leaf : Nat) (idxs : List Nat)
    (h : deriveStatelessInputs suite params rRand pkSeed pkRoot mu = some (leaf, idxs)) :
    leaf < 2 ^ (params.numLayers * params.subtreeHeight) := by
  unfold deriveStatelessInputs at h
  split at h
  · cases h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]
    exact Nat.mod_lt _ (Nat.two_pow_pos _)

/-- Regression: a stateful profile cannot enter the stateless derivation path. -/
theorem stateless_inputs_reject_stateful (suite : TweakableHashSuite) (params : PqHashParams)
    (rRand pkSeed pkRoot mu : List UInt8) (h : params.statefulJorts = true) :
    deriveStatelessInputs suite params rRand pkSeed pkRoot mu = none := by
  simp only [deriveStatelessInputs, h, Bool.or_true, ↓reduceIte]

def verifyHypertreeLayers (suite : TweakableHashSuite) (params : PqHashParams)
    (pkSeed pkRoot : List UInt8) (layer0Rand : List UInt8) :
    Nat → Nat → List UInt8 → List LayerXmssSig → Option (List UInt8)
  | _, _, curRoot, [] => some curRoot
  | layerIdx, globalIdx, curRoot, lsig :: rest =>
    let subLeaves := 2 ^ params.subtreeHeight
    let kpIdx := globalIdx % subLeaves
    let kpU32 := UInt32.ofNat kpIdx
    let treeIdxNat := globalIdx / subLeaves
    let treeIdx := UInt64.ofNat treeIdxNat
    let layerU32 := UInt32.ofNat layerIdx
    let hmsg := thHashMsg suite layer0Rand pkSeed pkRoot curRoot layerU32 treeIdx kpU32 lsig.tswCtr
    let digits := extractBaseWDigits params.w params.ell1 hmsg
    if !(checkTargetSum params.w params.ell1 params.targetSum digits) then none
    else if lsig.wotsChains.length ≠ params.ell1 then none
    else
      let wotsPk := recoverWotsPkFromSig suite params pkSeed layerU32 treeIdx kpIdx digits lsig.wotsChains
      match walkMerkleAuthPath suite pkSeed layerU32 treeIdx .tree params.subtreeHeight 0 kpIdx wotsPk lsig.authPath with
      | none => none
      | some nextSubtreeRoot =>
        -- `[P0-02]` Upper XMSS layers (`layerIdx + 1 ≥ 1`) ALWAYS pass `[]` (`0` `rRand` dependence)!
        verifyHypertreeLayers suite params pkSeed pkRoot [] (layerIdx + 1) treeIdxNat nextSubtreeRoot rest

/-- **Unified Verifier (`verifyPqHashSig`)** for stateless `Corduroy`/`Baggy` and stateful `Jorts`.
    `[P0-02]`/`[P1-04]`: binds `kp0` in `thHashMsg`, and passes `[]` (`0` `rRand` dependence) into
    `verifyHypertreeLayers` in stateless mode so static `forsPk` and all upper XMSS roots are signed
    deterministically! -/
@[expose] def verifyPqHashSig (suite : TweakableHashSuite) (params : PqHashParams)
    (pk : PqPublicKey) (msg : List UInt8) (sig : PqHashSig) : Bool :=
  if !(params.wellFormed) then false
  else if sig.layerSigs.length ≠ params.numLayers then false
  else if !(sig.leafGlobalIdx < 2 ^ (params.numLayers * params.subtreeHeight)) then false
  else
    let mu := thPreHash suite pk.pkSeed pk.pkRoot msg
    if params.statefulJorts then
      if !sig.forsOpenings.isEmpty || sig.msgTswCtr ≠ 0 then false
      else
        match verifyHypertreeLayers suite params pk.pkSeed pk.pkRoot sig.rRand 0 sig.leafGlobalIdx mu sig.layerSigs with
        | some computedTopRoot => decide (computedTopRoot = pk.pkRoot)
        | none => false
    else
      let subLeaves := 2 ^ params.subtreeHeight
      let kp0 := sig.leafGlobalIdx % subLeaves
      let kp0U32 := UInt32.ofNat kp0
      let tree0 := UInt64.ofNat (sig.leafGlobalIdx / subLeaves)
      let hmsg0 := thHashMsg suite sig.rRand pk.pkSeed pk.pkRoot mu 0 tree0 kp0U32 sig.msgTswCtr
      let digits0 := extractBaseWDigits params.w params.ell1 hmsg0
      if !(checkTargetSum params.w params.ell1 params.targetSum digits0) then false
      else
        match recoverForsPk suite params pk.pkSeed tree0 kp0 hmsg0 sig.forsOpenings with
        | none => false
        | some forsPk =>
          match verifyHypertreeLayers suite params pk.pkSeed pk.pkRoot [] 0 sig.leafGlobalIdx forsPk sig.layerSigs with
          | some computedTopRoot => decide (computedTopRoot = pk.pkRoot)
          | none => false

def signHypertreeLayers (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (pkRoot layer0Rand : List UInt8) (maxGrind : Nat) :
    Nat → Nat → List UInt8 → Nat → Option (List LayerXmssSig)
  | _, _, _, 0 => some []
  | layerIdx, globalIdx, curRoot, rem + 1 =>
    let subLeaves := 2 ^ params.subtreeHeight
    let kpIdx := globalIdx % subLeaves
    let kpU32 := UInt32.ofNat kpIdx
    let treeIdxNat := globalIdx / subLeaves
    let treeIdx := UInt64.ofNat treeIdxNat
    let layerU32 := UInt32.ofNat layerIdx
    match grindTswCounterAux suite params.w params.ell1 params.targetSum
            layer0Rand sk.pkSeed pkRoot curRoot layerU32 treeIdx kpU32 0 maxGrind with
    | none => none
    | some (ctr, digits, _) =>
      let wotsChains := (List.range params.ell1).map fun r =>
        let dr := digits.getD r 0
        wotsChainSteps suite sk.pkSeed layerU32 treeIdx kpIdx r 0 dr
          (wotsSecretBase suite sk layerU32 treeIdx kpIdx r)
      let authPath := buildMerkleAuthPath suite sk.pkSeed layerU32 treeIdx .tree
        (computeWotsPk suite params sk layerU32 treeIdx) params.subtreeHeight 0 kpIdx
      let nextRoot := computeXmssSubtreeRoot suite params sk layerU32 treeIdx
      match signHypertreeLayers suite params sk pkRoot [] maxGrind (layerIdx + 1) treeIdxNat nextRoot rem with
      | none => none
      | some restSigs =>
        some ({ tswCtr := ctr, wotsChains := wotsChains, authPath := authPath } :: restSigs)

def buildForsOpenings (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (tree0 : UInt64) (kp0 : Nat) (hmsg0 : List UInt8) : List ForsTreeOpening :=
  let idxs := deriveForsIndices params.forsTrees params.forsHeight hmsg0
  let leafFn := forsLeafFn suite sk tree0 kp0
  (List.range params.forsTrees).map fun j =>
    let idxJ := idxs.getD j 0
    let globalU := j * (2 ^ params.forsHeight) + idxJ
    let secVal := forsSecretLeaf suite sk tree0 kp0 globalU
    let path := buildMerkleAuthPath suite sk.pkSeed 0 tree0 .forsTree leafFn params.forsHeight j idxJ
    { secretVal := secVal, authPath := path }

def computeForsPk (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (tree0 : UInt64) (kp0 : Nat) : List UInt8 :=
  let leafFn := forsLeafFn suite sk tree0 kp0
  let roots := (List.range params.forsTrees).map fun j =>
    computeMerkleNode suite sk.pkSeed 0 tree0 .forsTree leafFn params.forsHeight j
  thTweakTl suite sk.pkSeed ⟨0, tree0, .forsRoots, UInt32.ofNat kp0, 0, 0⟩ roots

theorem signHypertreeLayers_zero (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (pkRoot layer0Rand : List UInt8) (maxGrind layerIdx globalIdx : Nat) (curRoot : List UInt8) :
    signHypertreeLayers suite params sk pkRoot layer0Rand maxGrind layerIdx globalIdx curRoot 0 = some [] := by rfl

theorem signHypertreeLayers_succ (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (pkRoot layer0Rand : List UInt8) (maxGrind layerIdx globalIdx : Nat) (curRoot : List UInt8) (rem : Nat) :
    signHypertreeLayers suite params sk pkRoot layer0Rand maxGrind layerIdx globalIdx curRoot (rem + 1) =
      let subLeaves := 2 ^ params.subtreeHeight
      let kpIdx := globalIdx % subLeaves
      let kpU32 := UInt32.ofNat kpIdx
      let treeIdxNat := globalIdx / subLeaves
      let treeIdx := UInt64.ofNat treeIdxNat
      let layerU32 := UInt32.ofNat layerIdx
      match grindTswCounterAux suite params.w params.ell1 params.targetSum
              layer0Rand sk.pkSeed pkRoot curRoot layerU32 treeIdx kpU32 0 maxGrind with
      | none => none
      | some (ctr, digits, _) =>
        let wotsChains := (List.range params.ell1).map fun r =>
          wotsChainSteps suite sk.pkSeed layerU32 treeIdx kpIdx r 0 (digits.getD r 0)
            (wotsSecretBase suite sk layerU32 treeIdx kpIdx r)
        let authPath := buildMerkleAuthPath suite sk.pkSeed layerU32 treeIdx .tree
          (computeWotsPk suite params sk layerU32 treeIdx) params.subtreeHeight 0 kpIdx
        let nextRoot := computeXmssSubtreeRoot suite params sk layerU32 treeIdx
        match signHypertreeLayers suite params sk pkRoot [] maxGrind (layerIdx + 1) treeIdxNat nextRoot rem with
        | none => none
        | some restSigs =>
          some ({ tswCtr := ctr, wotsChains := wotsChains, authPath := authPath } :: restSigs) := by rfl

theorem buildForsOpenings_eq (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (tree0 : UInt64) (kp0 : Nat) (hmsg0 : List UInt8) :
    buildForsOpenings suite params sk tree0 kp0 hmsg0 =
      let idxs := deriveForsIndices params.forsTrees params.forsHeight hmsg0
      let leafFn := forsLeafFn suite sk tree0 kp0
      (List.range params.forsTrees).map fun j =>
        let idxJ := idxs.getD j 0
        let globalU := j * (2 ^ params.forsHeight) + idxJ
        { secretVal := forsSecretLeaf suite sk tree0 kp0 globalU
          authPath := buildMerkleAuthPath suite sk.pkSeed 0 tree0 .forsTree leafFn params.forsHeight j idxJ } := by rfl

theorem computeForsPk_eq (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (tree0 : UInt64) (kp0 : Nat) :
    computeForsPk suite params sk tree0 kp0 =
      let leafFn := forsLeafFn suite sk tree0 kp0
      let roots := (List.range params.forsTrees).map fun j =>
        computeMerkleNode suite sk.pkSeed 0 tree0 .forsTree leafFn params.forsHeight j
      thTweakTl suite sk.pkSeed ⟨0, tree0, .forsRoots, UInt32.ofNat kp0, 0, 0⟩ roots := by rfl

/-- **Single-Party Reference Signer (`evalSingleSign`)**.
    `[P0-02]`/`[P1-04]`: binds `kp0` in `grindTswCounterAux` and signs static `forsPk` + all upper
    XMSS layers deterministically (`layer0Rand = []`) so stateless leaf collisions reveal identical
    WOTS+C codewords! -/
@[expose] def evalSingleSign (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (msg optRand : List UInt8)
    (leafGlobalIdx maxGrind : Nat) : Option PqHashSig :=
  if !(params.wellFormed) then none
  else if !(leafGlobalIdx < 2 ^ (params.numLayers * params.subtreeHeight)) then none
  else
    let pk := derivePublicKey suite params sk
    let mu := thPreHash suite pk.pkSeed pk.pkRoot msg
    let rRand := thPrfMsg suite sk.skPrf optRand mu
    if params.statefulJorts then
      match signHypertreeLayers suite params sk pk.pkRoot rRand maxGrind 0 leafGlobalIdx mu params.numLayers with
      | none => none
      | some layerSigs =>
        some { rRand := rRand, msgTswCtr := 0, leafGlobalIdx := leafGlobalIdx, forsOpenings := [], layerSigs := layerSigs }
    else
      let subLeaves := 2 ^ params.subtreeHeight
      let kp0 := leafGlobalIdx % subLeaves
      let kp0U32 := UInt32.ofNat kp0
      let tree0 := UInt64.ofNat (leafGlobalIdx / subLeaves)
      match grindTswCounterAux suite params.w params.ell1 params.targetSum
              rRand pk.pkSeed pk.pkRoot mu 0 tree0 kp0U32 0 maxGrind with
      | none => none
      | some (ctr0, _, hmsg0) =>
        let forsOps := buildForsOpenings suite params sk tree0 kp0 hmsg0
        let forsPk := computeForsPk suite params sk tree0 kp0
        match signHypertreeLayers suite params sk pk.pkRoot [] maxGrind 0 leafGlobalIdx forsPk params.numLayers with
        | none => none
        | some layerSigs =>
          some { rRand := rRand, msgTswCtr := ctr0, leafGlobalIdx := leafGlobalIdx, forsOpenings := forsOps, layerSigs := layerSigs }

/-- **`[P0-02]` Stateless Leaf-Reuse WOTS+C Determinism (`stateless_leaf_reuse_identical_wots_chains`)**:
    In stateless mode (`params.statefulJorts = false`), signing ANY two messages `(msg₁, optRand₁)`
    and `(msg₂, optRand₂)` at the same `leafGlobalIdx` produces **bit-for-bit identical** hypertree
    `layerSigs` across all `d` XMSS layers (`0` WOTS+C two-time codeword exposure!). -/
theorem stateless_leaf_reuse_identical_wots_chains
    (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey)
    (msg₁ optRand₁ msg₂ optRand₂ : List UInt8) (leafGlobalIdx maxGrind : Nat)
    {sig₁ sig₂ : PqHashSig}
    (hStateless : params.statefulJorts = false)
    (hSign₁ : evalSingleSign suite params sk msg₁ optRand₁ leafGlobalIdx maxGrind = some sig₁)
    (hSign₂ : evalSingleSign suite params sk msg₂ optRand₂ leafGlobalIdx maxGrind = some sig₂) :
    sig₁.layerSigs = sig₂.layerSigs := by
  unfold evalSingleSign at hSign₁ hSign₂
  cases hWf : params.wellFormed
  · simp [hWf] at hSign₁
  · cases hLeaf : decide (leafGlobalIdx < 2 ^ (params.numLayers * params.subtreeHeight))
    · simp [hWf, hLeaf] at hSign₁
    · simp only [hWf, hLeaf, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hStateless] at hSign₁ hSign₂
      cases hG1 : grindTswCounterAux suite params.w params.ell1 params.targetSum
          (thPrfMsg suite sk.skPrf optRand₁ (thPreHash suite (derivePublicKey suite params sk).pkSeed (derivePublicKey suite params sk).pkRoot msg₁))
          (derivePublicKey suite params sk).pkSeed (derivePublicKey suite params sk).pkRoot
          (thPreHash suite (derivePublicKey suite params sk).pkSeed (derivePublicKey suite params sk).pkRoot msg₁)
          0 (UInt64.ofNat (leafGlobalIdx / 2 ^ params.subtreeHeight)) (UInt32.ofNat (leafGlobalIdx % 2 ^ params.subtreeHeight)) 0 maxGrind
      · rw [hG1] at hSign₁; cases hSign₁
      · cases hG2 : grindTswCounterAux suite params.w params.ell1 params.targetSum
            (thPrfMsg suite sk.skPrf optRand₂ (thPreHash suite (derivePublicKey suite params sk).pkSeed (derivePublicKey suite params sk).pkRoot msg₂))
            (derivePublicKey suite params sk).pkSeed (derivePublicKey suite params sk).pkRoot
            (thPreHash suite (derivePublicKey suite params sk).pkSeed (derivePublicKey suite params sk).pkRoot msg₂)
            0 (UInt64.ofNat (leafGlobalIdx / 2 ^ params.subtreeHeight)) (UInt32.ofNat (leafGlobalIdx % 2 ^ params.subtreeHeight)) 0 maxGrind
        · rw [hG2] at hSign₂; cases hSign₂
        · rw [hG1] at hSign₁; rw [hG2] at hSign₂
          dsimp only at hSign₁ hSign₂
          cases hLs : signHypertreeLayers suite params sk (derivePublicKey suite params sk).pkRoot [] maxGrind 0 leafGlobalIdx
              (computeForsPk suite params sk (UInt64.ofNat (leafGlobalIdx / 2 ^ params.subtreeHeight)) (leafGlobalIdx % 2 ^ params.subtreeHeight)) params.numLayers
          · rw [hLs] at hSign₁; cases hSign₁
          · rw [hLs] at hSign₁ hSign₂
            simp only [Option.some.injEq] at hSign₁ hSign₂
            rw [← hSign₁, ← hSign₂]

theorem signHypertreeLayers_sound
    (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (pkRoot : List UInt8) (maxGrind : Nat) :
    ∀ (rem layerIdx globalIdx : Nat) (layer0Rand curRoot : List UInt8) (layerSigs : List LayerXmssSig),
      0 < rem →
      globalIdx < 2 ^ (rem * params.subtreeHeight) →
      signHypertreeLayers suite params sk pkRoot layer0Rand maxGrind layerIdx globalIdx curRoot rem = some layerSigs →
      layerSigs.length = rem ∧
      verifyHypertreeLayers suite params sk.pkSeed pkRoot layer0Rand layerIdx globalIdx curRoot layerSigs =
        some (computeXmssSubtreeRoot suite params sk (UInt32.ofNat (layerIdx + rem - 1)) 0)
  | 0, _, _, _, _, _, hPos, _, _ => by omega
  | 1, layerIdx, globalIdx, layer0Rand, curRoot, layerSigs, _, hIdxLt, hSign => by
    rw [signHypertreeLayers] at hSign
    cases hGrind : grindTswCounterAux suite params.w params.ell1 params.targetSum
        layer0Rand sk.pkSeed pkRoot curRoot (UInt32.ofNat layerIdx)
        (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight))
        (UInt32.ofNat (globalIdx % 2 ^ params.subtreeHeight)) 0 maxGrind with
    | none => rw [hGrind] at hSign; cases hSign
    | some triple =>
      rcases triple with ⟨ctr, digits, hmsgG⟩
      rw [hGrind] at hSign
      simp only [signHypertreeLayers, Option.some.injEq] at hSign
      subst hSign
      obtain ⟨hMsgEq, hDigEq, hChk⟩ := grindTswCounterAux_sound hGrind
      have hSubPos : 0 < 2 ^ params.subtreeHeight := Nat.two_pow_pos _
      have hGlobalBound : globalIdx < 2 ^ params.subtreeHeight := by simpa [Nat.one_mul] using hIdxLt
      have hDiv0 : globalIdx / 2 ^ params.subtreeHeight = 0 := Nat.div_eq_of_lt hGlobalBound
      refine ⟨rfl, ?_⟩
      simp only [verifyHypertreeLayers]
      rw [← hMsgEq, ← hDigEq, hChk]
      have hChainsLen : ((List.range params.ell1).map fun r =>
          wotsChainSteps suite sk.pkSeed (UInt32.ofNat layerIdx)
            (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight))
            (globalIdx % 2 ^ params.subtreeHeight) r 0 (digits.getD r 0)
            (wotsSecretBase suite sk (UInt32.ofNat layerIdx)
              (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight))
              (globalIdx % 2 ^ params.subtreeHeight) r)).length = params.ell1 := by simp
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hChainsLen, ne_eq, not_true_eq_false]
      have hWotsEq := recoverWotsPkFromSig_eq_computeWotsPk suite params sk
        (UInt32.ofNat layerIdx) (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight))
        (globalIdx % 2 ^ params.subtreeHeight) digits hChk
      dsimp only at hWotsEq
      rw [hWotsEq]
      have hWalk := walkMerkleAuthPath_buildMerkleAuthPath suite sk.pkSeed
        (UInt32.ofNat layerIdx) (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight)) .tree
        (computeWotsPk suite params sk (UInt32.ofNat layerIdx) (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight)))
        params.subtreeHeight 0 (globalIdx % 2 ^ params.subtreeHeight) (Nat.mod_lt _ hSubPos)
      simp only [Nat.zero_mul, Nat.zero_add] at hWalk
      rw [hWalk]
      simp only [computeXmssSubtreeRoot, hDiv0, Nat.add_sub_cancel]
      rfl
  | rem + 2, layerIdx, globalIdx, layer0Rand, curRoot, layerSigs, _, hIdxLt, hSign => by
    rw [signHypertreeLayers] at hSign
    dsimp only at hSign
    cases hGrind : grindTswCounterAux suite params.w params.ell1 params.targetSum
        layer0Rand sk.pkSeed pkRoot curRoot (UInt32.ofNat layerIdx)
        (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight))
        (UInt32.ofNat (globalIdx % 2 ^ params.subtreeHeight)) 0 maxGrind with
    | none => rw [hGrind] at hSign; cases hSign
    | some triple =>
      rcases triple with ⟨ctr, digits, hmsgG⟩
      rw [hGrind] at hSign
      dsimp only at hSign
      cases hRest : signHypertreeLayers suite params sk pkRoot [] maxGrind
          (layerIdx + 1) (globalIdx / 2 ^ params.subtreeHeight)
          (computeXmssSubtreeRoot suite params sk (UInt32.ofNat layerIdx)
            (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight))) (rem + 1) with
      | none => rw [hRest] at hSign; cases hSign
      | some restSigs =>
        rw [hRest] at hSign
        simp only [Option.some.injEq] at hSign
        subst hSign
        obtain ⟨hMsgEq, hDigEq, hChk⟩ := grindTswCounterAux_sound hGrind
        have hSubPos : 0 < 2 ^ params.subtreeHeight := Nat.two_pow_pos _
        have hTreeLt : globalIdx / 2 ^ params.subtreeHeight < 2 ^ ((rem + 1) * params.subtreeHeight) := by
          have hPow : 2 ^ ((rem + 2) * params.subtreeHeight) =
              2 ^ ((rem + 1) * params.subtreeHeight) * 2 ^ params.subtreeHeight := by
            rw [Nat.succ_mul, Nat.pow_add]
          exact (Nat.div_lt_iff_lt_mul hSubPos).mpr (hPow ▸ hIdxLt)
        obtain ⟨hRestLen, hRestVer⟩ := signHypertreeLayers_sound suite params sk pkRoot maxGrind
          (rem + 1) (layerIdx + 1) (globalIdx / 2 ^ params.subtreeHeight) []
          (computeXmssSubtreeRoot suite params sk (UInt32.ofNat layerIdx)
            (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight)))
          restSigs (by omega) hTreeLt hRest
        refine ⟨by simp [hRestLen], ?_⟩
        simp only [verifyHypertreeLayers]
        change (let hmsg := thHashMsg suite layer0Rand sk.pkSeed pkRoot curRoot
                  (UInt32.ofNat layerIdx) (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight))
                  (UInt32.ofNat (globalIdx % 2 ^ params.subtreeHeight)) ctr; _) = _
        rw [← hMsgEq, ← hDigEq, hChk]
        have hChainsLen : ((List.range params.ell1).map fun r =>
            wotsChainSteps suite sk.pkSeed (UInt32.ofNat layerIdx)
              (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight))
              (globalIdx % 2 ^ params.subtreeHeight) r 0 (digits.getD r 0)
              (wotsSecretBase suite sk (UInt32.ofNat layerIdx)
                (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight))
                (globalIdx % 2 ^ params.subtreeHeight) r)).length = params.ell1 := by simp
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hChainsLen, ne_eq, not_true_eq_false]
        have hWotsEq := recoverWotsPkFromSig_eq_computeWotsPk suite params sk
          (UInt32.ofNat layerIdx) (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight))
          (globalIdx % 2 ^ params.subtreeHeight) digits hChk
        dsimp only at hWotsEq
        rw [hWotsEq]
        have hWalk := walkMerkleAuthPath_buildMerkleAuthPath suite sk.pkSeed
          (UInt32.ofNat layerIdx) (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight)) .tree
          (computeWotsPk suite params sk (UInt32.ofNat layerIdx)
            (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight)))
          params.subtreeHeight 0 (globalIdx % 2 ^ params.subtreeHeight) (Nat.mod_lt _ hSubPos)
        simp only [Nat.zero_mul, Nat.zero_add] at hWalk
        rw [hWalk]
        change verifyHypertreeLayers suite params sk.pkSeed pkRoot [] (layerIdx + 1)
            (globalIdx / 2 ^ params.subtreeHeight)
            (computeXmssSubtreeRoot suite params sk (UInt32.ofNat layerIdx)
              (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight))) restSigs = _
        rw [hRestVer]
        have hTopLayerEq : layerIdx + 1 + (rem + 1) - 1 = layerIdx + (rem + 2) - 1 := by omega
        rw [hTopLayerEq]

private theorem list_range_succ_shift {α : Type} (rem : Nat) (f : Nat → α) :
    (List.range (rem + 1)).map f = f 0 :: (List.range rem).map (fun k => f (k + 1)) := by
  induction rem generalizing f with
  | zero => simp
  | succ r ih => rw [List.range_succ, List.map_append, ih f, List.range_succ, List.map_append]; simp

theorem recoverForsPk_buildForsOpenings
    (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (tree0 : UInt64) (kp0 : Nat) (hmsg0 : List UInt8) :
    recoverForsPk suite params sk.pkSeed tree0 kp0 hmsg0
      (buildForsOpenings suite params sk tree0 kp0 hmsg0) =
    some (computeForsPk suite params sk tree0 kp0) := by
  unfold recoverForsPk buildForsOpenings computeForsPk
  let idxs := deriveForsIndices params.forsTrees params.forsHeight hmsg0
  let leafFn := forsLeafFn suite sk tree0 kp0
  let ops := (List.range params.forsTrees).map fun j =>
    let idxJ := idxs.getD j 0
    let globalU := j * (2 ^ params.forsHeight) + idxJ
    { secretVal := forsSecretLeaf suite sk tree0 kp0 globalU
      authPath := buildMerkleAuthPath suite sk.pkSeed 0 tree0 .forsTree leafFn params.forsHeight j idxJ : ForsTreeOpening }
  have hOpsLen : ops.length = params.forsTrees := by simp [ops]
  change (if ops.length ≠ params.forsTrees then none else _) = _
  simp only [hOpsLen, ne_eq, not_true_eq_false, ↓reduceIte]
  obtain ⟨hIdxsLen, hIdxsBound⟩ := deriveForsIndices_bounds params.forsTrees params.forsHeight hmsg0
  have hCollect : ∀ (rem j : Nat), j + rem = params.forsTrees →
      recoverForsTreeRoots suite params sk.pkSeed tree0 kp0 idxs ops j rem =
      some ((List.range rem).map fun off =>
        computeMerkleNode suite sk.pkSeed 0 tree0 .forsTree leafFn params.forsHeight (j + off)) := by
    intro rem
    induction rem with
    | zero => intro _ _; simp [recoverForsTreeRoots]
    | succ rem ih =>
      intro j hjSum
      have hjLt : j < params.forsTrees := by omega
      simp only [recoverForsTreeRoots]
      have hOpGet : ops.getD j (⟨[], []⟩ : ForsTreeOpening) =
          { secretVal := forsSecretLeaf suite sk tree0 kp0 (j * (2 ^ params.forsHeight) + idxs.getD j 0)
            authPath := buildMerkleAuthPath suite sk.pkSeed 0 tree0 .forsTree leafFn params.forsHeight j (idxs.getD j 0) } :=
        list_getD_map_range params.forsTrees _ (⟨[], []⟩ : ForsTreeOpening) hjLt
      rw [hOpGet]
      dsimp only
      have hIdxLt : idxs.getD j 0 < 2 ^ params.forsHeight := by
        have hjIdxs : j < idxs.length := hIdxsLen ▸ hjLt
        rw [list_getD_eq_getElem idxs 0 hjIdxs]
        exact hIdxsBound _ (List.getElem_mem hjIdxs)
      have hWalk := walkMerkleAuthPath_buildMerkleAuthPath suite sk.pkSeed 0 tree0 .forsTree
        leafFn params.forsHeight j (idxs.getD j 0) hIdxLt
      change (match walkMerkleAuthPath suite sk.pkSeed 0 tree0 .forsTree params.forsHeight j (idxs.getD j 0)
                (leafFn (j * (2 ^ params.forsHeight) + idxs.getD j 0))
                (buildMerkleAuthPath suite sk.pkSeed 0 tree0 .forsTree leafFn params.forsHeight j (idxs.getD j 0)) with
              | none => none
              | some rJ => _) = _
      rw [hWalk, ih (j + 1) (by omega), list_range_succ_shift]
      simp only [Nat.add_zero, Option.some.injEq, List.cons.injEq, true_and]
      apply List.map_congr_left
      intro k _
      have hAssoc : j + 1 + k = j + (k + 1) := by omega
      rw [hAssoc]
  change (match recoverForsTreeRoots suite params sk.pkSeed tree0 kp0 idxs ops 0 params.forsTrees with
          | none => none | some roots => _) = _
  rw [hCollect params.forsTrees 0 (by omega)]; simp; rfl

/-- **Unconditional Signature Completeness (`verifyPqHashSig_evalSingleSign`)**:
    Whenever `evalSingleSign` returns `some sig` (for ANY `TweakableHashSuite`, whether stateless
    `Corduroy` / `Baggy` or stateful `Jorts`), `verifyPqHashSig` accepts (`= true`). -/
theorem verifyPqHashSig_evalSingleSign
    (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (msg optRand : List UInt8)
    (leafGlobalIdx maxGrind : Nat) (sig : PqHashSig)
    (hSign : evalSingleSign suite params sk msg optRand leafGlobalIdx maxGrind = some sig) :
    verifyPqHashSig suite params (derivePublicKey suite params sk) msg sig = true := by
  unfold evalSingleSign at hSign
  cases hWf : params.wellFormed
  · simp [hWf] at hSign
  · rw [hWf] at hSign
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hSign
    have hDPos : 0 < params.numLayers := by
      simp only [PqHashParams.wellFormed, Bool.and_eq_true, decide_eq_true_eq] at hWf; omega
    cases hGuard2 : decide (leafGlobalIdx < 2 ^ (params.numLayers * params.subtreeHeight))
    · simp [hGuard2] at hSign
    · have hLeafLt : leafGlobalIdx < 2 ^ (params.numLayers * params.subtreeHeight) :=
        of_decide_eq_true hGuard2
      simp only [hLeafLt, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hSign
      dsimp only [derivePublicKey] at hSign
      cases hMode : params.statefulJorts
      · rw [hMode] at hSign
        simp only [Bool.false_eq_true, ↓reduceIte] at hSign
        cases hGrind0 : grindTswCounterAux suite params.w params.ell1 params.targetSum
            (thPrfMsg suite sk.skPrf optRand
              (thPreHash suite sk.pkSeed (computeXmssSubtreeRoot suite params sk (UInt32.ofNat (params.numLayers - 1)) 0) msg))
            sk.pkSeed (computeXmssSubtreeRoot suite params sk (UInt32.ofNat (params.numLayers - 1)) 0)
            (thPreHash suite sk.pkSeed (computeXmssSubtreeRoot suite params sk (UInt32.ofNat (params.numLayers - 1)) 0) msg)
            0 (UInt64.ofNat (leafGlobalIdx / 2 ^ params.subtreeHeight))
            (UInt32.ofNat (leafGlobalIdx % 2 ^ params.subtreeHeight)) 0 maxGrind with
        | none => rw [hGrind0] at hSign; cases hSign
        | some tr0 =>
          rcases tr0 with ⟨ctr0, dig0, hmsg0⟩
          rw [hGrind0] at hSign; dsimp only at hSign
          cases hLayers : signHypertreeLayers suite params sk
              (computeXmssSubtreeRoot suite params sk (UInt32.ofNat (params.numLayers - 1)) 0)
              [] maxGrind 0 leafGlobalIdx
              (computeForsPk suite params sk (UInt64.ofNat (leafGlobalIdx / 2 ^ params.subtreeHeight))
                (leafGlobalIdx % 2 ^ params.subtreeHeight)) params.numLayers with
          | none => rw [hLayers] at hSign; cases hSign
          | some layerSigs =>
            rw [hLayers] at hSign; simp only [Option.some.injEq] at hSign; subst hSign
            obtain ⟨hMsg0Eq, hDig0Eq, hChk0⟩ := grindTswCounterAux_sound hGrind0
            obtain ⟨hLsLen, hLsVer⟩ := signHypertreeLayers_sound suite params sk
              (computeXmssSubtreeRoot suite params sk (UInt32.ofNat (params.numLayers - 1)) 0)
              maxGrind params.numLayers 0 leafGlobalIdx []
              (computeForsPk suite params sk (UInt64.ofNat (leafGlobalIdx / 2 ^ params.subtreeHeight))
                (leafGlobalIdx % 2 ^ params.subtreeHeight)) layerSigs hDPos hLeafLt hLayers
            unfold verifyPqHashSig; dsimp only [derivePublicKey]
            simp only [hWf, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hLsLen, ne_eq, not_true_eq_false,
              hLeafLt, decide_true, hMode]
            rw [← hMsg0Eq, ← hDig0Eq, hChk0]; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
            rw [recoverForsPk_buildForsOpenings]; dsimp only; rw [hLsVer]; simp
      · rw [hMode] at hSign; simp only [↓reduceIte] at hSign
        cases hLayers : signHypertreeLayers suite params sk
            (computeXmssSubtreeRoot suite params sk (UInt32.ofNat (params.numLayers - 1)) 0)
            (thPrfMsg suite sk.skPrf optRand
              (thPreHash suite sk.pkSeed (computeXmssSubtreeRoot suite params sk (UInt32.ofNat (params.numLayers - 1)) 0) msg))
            maxGrind 0 leafGlobalIdx
            (thPreHash suite sk.pkSeed (computeXmssSubtreeRoot suite params sk (UInt32.ofNat (params.numLayers - 1)) 0) msg)
            params.numLayers with
        | none => rw [hLayers] at hSign; cases hSign
        | some layerSigs =>
          rw [hLayers] at hSign; simp only [Option.some.injEq] at hSign; subst hSign
          obtain ⟨hLsLen, hLsVer⟩ := signHypertreeLayers_sound suite params sk
            (computeXmssSubtreeRoot suite params sk (UInt32.ofNat (params.numLayers - 1)) 0)
            maxGrind params.numLayers 0 leafGlobalIdx
            (thPrfMsg suite sk.skPrf optRand
              (thPreHash suite sk.pkSeed (computeXmssSubtreeRoot suite params sk (UInt32.ofNat (params.numLayers - 1)) 0) msg))
            (thPreHash suite sk.pkSeed (computeXmssSubtreeRoot suite params sk (UInt32.ofNat (params.numLayers - 1)) 0) msg)
            layerSigs hDPos hLeafLt hLayers
          unfold verifyPqHashSig; dsimp only [derivePublicKey]
          simp only [hWf, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hLsLen, ne_eq, not_true_eq_false,
            hLeafLt, decide_true, hMode, List.isEmpty_nil]
          rw [hLsVer]; simp

/-! ### Constructive `0 Classical` `PSum` EUF-CMA Forgery Extractor & `ValidJortsBatch` -/

/-- Constructive `Type`-valued one-way chain inversion witness:
    exhibits `preimage` at chain step `step < revealedStep` hashing under `thChainF` to `revealedVal`. -/
structure WotsBackwardInversionWitness (suite : TweakableHashSuite) (pkSeed : List UInt8) where
  layer        : UInt32
  tree         : UInt64
  kp           : Nat
  chain        : Nat
  step         : Nat
  revealedStep : Nat
  step_lt      : step < revealedStep
  preimage     : List UInt8
  revealedVal  : List UInt8
  invertsChain : thChainF suite pkSeed ⟨layer, tree, .wotsHash, UInt32.ofNat kp, UInt32.ofNat chain, UInt32.ofNat step⟩ preimage = revealedVal

/-- Constructive chain-collision walker (`0 Classical`): if `u ≠ v` reach equal chain values after
    `rem` iterations of `thChainF`, pinpoints the exact first colliding step. -/
def extractChainCollision (suite : TweakableHashSuite) (pkSeed : List UInt8)
    (layer : UInt32) (tree : UInt64) (kp chain : Nat) :
    ∀ (rem startStep : Nat) (u v : List UInt8),
      u ≠ v →
      wotsChainSteps suite pkSeed layer tree kp chain startStep rem u =
        wotsChainSteps suite pkSeed layer tree kp chain startStep rem v →
      HashCollisionWitness suite.rawHash
  | 0, _, _, _, hNe, hEq => False.elim (hNe hEq)
  | rem + 1, startStep, u, v, hNe, hEq =>
    let adrs : HashAdrs := ⟨layer, tree, .wotsHash, UInt32.ofNat kp, UInt32.ofNat chain, UInt32.ofNat startStep⟩
    let fu := thChainF suite pkSeed adrs u
    let fv := thChainF suite pkSeed adrs v
    if hStepEq : fu = fv then
      match thCall_binds_or_collision suite hStepEq with
      | .inl ⟨_, _, _, hArgs⟩ => False.elim (hNe (by injection hArgs))
      | .inr col => col
    else
      extractChainCollision suite pkSeed layer tree kp chain rem (startStep + 1) fu fv hStepEq hEq

/-- **Constructive `0 Classical` WOTS+C / `TSW` EUF-CMA Forgery Extractor (`extractPqHashForgery`)**:
    Given an honestly revealed WOTS+C signature `honestChains` on `d₁` and any accepted forgery
    `forgedChains` on a distinct `TSW` digit vector `d₂ ≠ d₁` recovering the same `wotsPk`,
    constructively extracts `PSum (WotsBackwardInversionWitness suite pkSeed) (HashCollisionWitness suite.rawHash)`. -/
def extractPqHashForgery
    (suite : TweakableHashSuite) (params : PqHashParams)
    (pkSeed : List UInt8) (layer : UInt32) (tree : UInt64) (kp : Nat)
    (d₁ d₂ : List Nat) (honestChains forgedChains : List (List UInt8))
    (hValid₁ : checkTargetSum params.w params.ell1 params.targetSum d₁ = true)
    (hValid₂ : checkTargetSum params.w params.ell1 params.targetSum d₂ = true)
    (hDistinct : d₁ ≠ d₂)
    (hSameWotsPk : recoverWotsPkFromSig suite params pkSeed layer tree kp d₂ forgedChains =
                   recoverWotsPkFromSig suite params pkSeed layer tree kp d₁ honestChains) :
    PSum (WotsBackwardInversionWitness suite pkSeed) (HashCollisionWitness suite.rawHash) :=
  let end₂ := recoverWotsEndpoints suite params pkSeed layer tree kp d₂ forgedChains
  let end₁ := recoverWotsEndpoints suite params pkSeed layer tree kp d₁ honestChains
  if hEndNe : end₂ ≠ end₁ then
    match thCall_binds_or_collision suite hSameWotsPk with
    | .inl ⟨_, _, _, hEqEnds⟩ => False.elim (hEndNe hEqEnds)
    | .inr col => .inr col
  else
    have hEndEq : end₂ = end₁ := Decidable.of_not_not hEndNe
    have hIncomp := (tsw_incomparable_no_chain_forgery hValid₁ hValid₂ hDistinct).2
    have hComplete := findBackwardCoord_complete
      (let ⟨r', hr2, hr1, hlt, _⟩ := hIncomp; ⟨r', hr2, hr1, hlt⟩)
    match hFind : findBackwardCoord d₁ d₂ with
    | none =>
      False.elim (by obtain ⟨_, _, _, hSome, _⟩ := hComplete; rw [hFind] at hSome; cases hSome)
    | some r =>
      have hProps : ∃ (hr₂ : r < d₂.length) (hr₁ : r < d₁.length), d₂[r]'hr₂ < d₁[r]'hr₁ ∧ d₁[r]'hr₁ < params.w := by
        obtain ⟨r0, hr2, hr1, hSome, hlt⟩ := hComplete
        rw [hFind] at hSome
        injection hSome with hEqR
        subst hEqR
        obtain ⟨_, hB1, _⟩ := (checkTargetSum_iff _ _ _ d₁).mp hValid₁
        exact ⟨hr2, hr1, hlt, hB1 _ (List.getElem_mem hr1)⟩
      let s₂ := d₂.getD r 0
      let s₁ := d₁.getD r 0
      have hsLt : s₂ < s₁ ∧ s₁ < params.w ∧ r < params.ell1 := by
        obtain ⟨hr2, hr1, hlt, hbw⟩ := hProps
        obtain ⟨hL1, _, _⟩ := (checkTargetSum_iff _ _ _ d₁).mp hValid₁
        rw [show s₂ = d₂[r]'hr2 from list_getD_eq_getElem d₂ 0 hr2,
            show s₁ = d₁[r]'hr1 from list_getD_eq_getElem d₁ 0 hr1]
        exact ⟨hlt, hbw, hL1 ▸ hr1⟩
      let sig₂ := forgedChains.getD r []
      let sig₁ := honestChains.getD r []
      let gap := s₁ - s₂
      have hGapGe1 : 1 ≤ gap := Nat.succ_le_of_lt (Nat.sub_pos_of_lt hsLt.1)
      have hGapSplit : gap = (gap - 1) + 1 := (Nat.sub_add_cancel hGapGe1).symm
      have hsAdd : s₂ + gap = s₁ := Nat.add_sub_of_le (Nat.le_of_lt hsLt.1)
      let mid₂ := wotsChainSteps suite pkSeed layer tree kp r s₂ gap sig₂
      if hMidEq : mid₂ = sig₁ then
        let preStep := s₂ + (gap - 1)
        let preVal := wotsChainSteps suite pkSeed layer tree kp r s₂ (gap - 1) sig₂
        .inl
          { layer := layer, tree := tree, kp := kp, chain := r
            step := preStep, revealedStep := s₁
            step_lt := by
              calc
                s₂ + (gap - 1) < (s₂ + (gap - 1)) + 1 := Nat.lt_succ_self _
                _ = s₂ + ((gap - 1) + 1) := Nat.add_assoc _ _ 1
                _ = s₂ + gap := by rw [← hGapSplit]
                _ = s₁ := hsAdd
            preimage := preVal, revealedVal := sig₁
            invertsChain := by
              have hCompose := wotsChainSteps_add suite pkSeed layer tree kp r (gap - 1) 1 s₂ sig₂
              rw [← hGapSplit] at hCompose
              simpa only [wotsChainSteps] using hCompose.trans hMidEq }
      else
        have hEndAtR : end₂.getD r [] = end₁.getD r [] := by rw [hEndEq]
        have hEnd2R : end₂.getD r [] = wotsChainSteps suite pkSeed layer tree kp r s₂ ((params.w - 1) - s₂) sig₂ :=
          list_getD_map_range params.ell1 _ [] hsLt.2.2
        have hEnd1R : end₁.getD r [] = wotsChainSteps suite pkSeed layer tree kp r s₁ ((params.w - 1) - s₁) sig₁ :=
          list_getD_map_range params.ell1 _ [] hsLt.2.2
        have hRemEq : wotsChainSteps suite pkSeed layer tree kp r s₁ ((params.w - 1) - s₁) mid₂ =
            wotsChainSteps suite pkSeed layer tree kp r s₁ ((params.w - 1) - s₁) sig₁ := by
          have hs1Le : s₁ ≤ params.w - 1 := Nat.le_sub_one_of_lt hsLt.2.1
          have hSplit : (params.w - 1) - s₂ = gap + ((params.w - 1) - s₁) := by
            have hSum : s₂ + (gap + ((params.w - 1) - s₁)) = params.w - 1 := by
              rw [← Nat.add_assoc, hsAdd, Nat.add_sub_of_le hs1Le]
            exact (congrArg (· - s₂) hSum).symm.trans (Nat.add_sub_cancel_left s₂ _)
          have hStep := wotsChainSteps_add suite pkSeed layer tree kp r gap ((params.w - 1) - s₁) s₂ sig₂
          rw [hsAdd, ← hSplit] at hStep
          rw [hStep, ← hEnd2R, hEndAtR, hEnd1R]
        .inr (extractChainCollision suite pkSeed layer tree kp r ((params.w - 1) - s₁) s₁
                mid₂ sig₁ hMidEq hRemEq)

/-- Single validator entry for STARK-aggregated `Jorts-Poseidon2` batch verification. -/
structure JortsBatchItem where
  validatorPk : PqPublicKey
  message     : List UInt8
  signature   : PqHashSig
  deriving DecidableEq, Repr

/-- Batch verification relation over `Poseidon2` `Jorts` signatures. -/
def ValidJortsBatch (params : PqHashParams) (items : List JortsBatchItem) : Bool :=
  decide (params.statefulJorts = true) &&
  decide (items ≠ []) &&
  decide (items.map (fun item => (item.validatorPk, item.signature.leafGlobalIdx))).Nodup &&
  items.all (fun item => verifyPqHashSig poseidon2Suite params item.validatorPk item.message item.signature)

theorem validJortsBatch_sound {params : PqHashParams} {items : List JortsBatchItem}
    (h : ValidJortsBatch params items = true) :
    params.statefulJorts = true ∧
    ∀ item ∈ items, verifyPqHashSig poseidon2Suite params item.validatorPk item.message item.signature = true := by
  simp only [ValidJortsBatch, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  exact ⟨h.1.1.1, h.2⟩

/-- A batch cannot be empty or replay a validator at the same epoch. -/
theorem validJortsBatch_fresh {params : PqHashParams} {items : List JortsBatchItem}
    (h : ValidJortsBatch params items = true) :
    items ≠ [] ∧ (items.map (fun item => (item.validatorPk, item.signature.leafGlobalIdx))).Nodup := by
  simp only [ValidJortsBatch, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.2, h.1.2⟩

theorem empty_jorts_batch_rejected (params : PqHashParams) :
    ValidJortsBatch params [] = false := by
  simp [ValidJortsBatch]

/-! ## 5. Committed-Identity Hybrid Combiner (`HybridPinnedSig`) & Tri-State `VerifyReply` -/

def hybridIdCustom : List UInt8 := "QSAG.PQ.HYBRID.ID/v1".toUTF8.toList

/-- Enrolled identity digest `idCommit = cSHAKE256("QSAG.PQ.HYBRID.ID/v1", encodeMultiFrame [pk₁, pk₂])`. -/
@[expose] def computeHybridIdCommit (pk1Bytes pk2Bytes : List UInt8) : List UInt8 :=
  cshake256Bytes hybridIdCustom (encodeMultiFrame [pk1Bytes, pk2Bytes])

/-- Constructive `0 Classical` binding proof for `computeHybridIdCommit`. -/
def computeHybridIdCommit_binds {a₁ b₁ a₂ b₂ : List UInt8}
    (hEq : computeHybridIdCommit a₁ b₁ = computeHybridIdCommit a₂ b₂) :
    PSum (a₁ = a₂ ∧ b₁ = b₂) (HashCollisionWitness (cshake256Bytes hybridIdCustom)) :=
  if hFrame : encodeMultiFrame [a₁, b₁] = encodeMultiFrame [a₂, b₂] then
    .inl (by
      have hList := encodeMultiFrame_injective hFrame
      simp only [List.cons.injEq, and_true] at hList
      exact hList)
  else
    .inr { m1 := encodeMultiFrame [a₁, b₁]
           m2 := encodeMultiFrame [a₂, b₂]
           ne := hFrame
           eq := hEq }

/-- Wire envelope carrying component signature `sig1`, candidate `carriedPk2`, and PQ signature `sig2`. -/
structure HybridWireSig (Sig₁ PK₂ Sig₂ : Type) where
  sig1       : Sig₁
  carriedPk2 : PK₂
  sig2       : Sig₂
  deriving DecidableEq, Repr

/-- **Load-Bearing Committed-Identity Pinning Check (`checkHybridPinning`)**:
    Refuses self-carried `carriedPk2` substitution unless `(pk1, carriedPk2)` hashes to `idCommit`. -/
@[expose] def checkHybridPinning {PK₁ PK₂ : Type}
    (enc1 : PK₁ → List UInt8) (enc2 : PK₂ → List UInt8)
    (idCommit : List UInt8) (pk1 : PK₁) (carriedPk2 : PK₂) : Bool :=
  decide (computeHybridIdCommit (enc1 pk1) (enc2 carriedPk2) = idCommit)

/-- Exact multi-key message envelope signed by both hybrid components. -/
def buildHybridBoundMessage (idCommit pk1 pk2 msg : List UInt8) : List UInt8 :=
  encodeMultiFrame ["QSAG.PQ.HYBRID.MSG/v1".toUTF8.toList, idCommit, pk1, pk2, msg]

theorem hybrid_bound_message_injective {id₁ pk₁ pq₁ m₁ id₂ pk₂ pq₂ m₂ : List UInt8}
    (h : buildHybridBoundMessage id₁ pk₁ pq₁ m₁ = buildHybridBoundMessage id₂ pk₂ pq₂ m₂) :
    id₁ = id₂ ∧ pk₁ = pk₂ ∧ pq₁ = pq₂ ∧ m₁ = m₂ := by
  have he := encodeMultiFrame_injective h
  simpa only [List.cons.injEq, true_and, and_true] using he

/-- Framing strictly increases the message length, so a hybrid payload cannot equal its raw message. -/
theorem hybrid_bound_message_ne_raw (id pk pq msg : List UInt8) :
    buildHybridBoundMessage id pk pq msg ≠ msg := by
  intro h
  have hl := congrArg List.length h
  simp only [buildHybridBoundMessage, encodeMultiFrame, encodeByteFields_cons,
    encodeByteFields_nil, encodeListField_eq, List.length_append, List.length_cons,
    List.length_nil, Nat.reduceAdd] at hl
  have hp := leb128_length_pos 5
  omega

/-- Both verifiers consume the same framed identity, partner keys and message. -/
def verifyHybridPinnedSig {PK₁ SK₁ Sig₁ PK₂ SK₂ Sig₂ : Type}
    (S₁ : AbstractSigScheme PK₁ SK₁ (List UInt8) Sig₁)
    (S₂ : AbstractSigScheme PK₂ SK₂ (List UInt8) Sig₂)
    (enc1 : PK₁ → List UInt8) (enc2 : PK₂ → List UInt8)
    (idCommit : List UInt8) (pk1 : PK₁) (msg : List UInt8)
    (hsig : HybridWireSig Sig₁ PK₂ Sig₂) : Bool :=
  let bound := buildHybridBoundMessage idCommit (enc1 pk1) (enc2 hsig.carriedPk2) msg
  checkHybridPinning enc1 enc2 idCommit pk1 hsig.carriedPk2 &&
  S₁.verify pk1 bound hsig.sig1 && S₂.verify hsig.carriedPk2 bound hsig.sig2

/-- Concrete regression scheme: a signature is the signed bytes. Raw signatures fail the framed gate. -/
def byteEqualitySignature : AbstractSigScheme Unit Unit (List UInt8) (List UInt8) where
  sign _ msg := msg
  verify _ msg sig := decide (msg = sig)
  complete _ _ := True
  completeness := by intro pk sk h msg; exact decide_eq_true rfl

theorem hybrid_raw_bytes_regression (id pk pq msg : List UInt8) :
    verifyHybridPinnedSig byteEqualitySignature byteEqualitySignature
      (fun _ => pk) (fun _ => pq) id () msg ⟨msg, (), msg⟩ = false := by
  simp only [verifyHybridPinnedSig, byteEqualitySignature,
    decide_eq_false (hybrid_bound_message_ne_raw id pk pq msg), Bool.and_false]

/-- Acceptance binds both signatures to the enrolled partner, or exposes a distinct-input collision. -/
theorem hybrid_ucRealizes_if_either_secure
    {PK₁ SK₁ Sig₁ PK₂ SK₂ Sig₂ : Type}
    (S₁ : AbstractSigScheme PK₁ SK₁ (List UInt8) Sig₁)
    (S₂ : AbstractSigScheme PK₂ SK₂ (List UInt8) Sig₂)
    (enc1 : PK₁ → List UInt8) (enc2 : PK₂ → List UInt8)
    (hEnc2Inj : ∀ {x y : PK₂}, enc2 x = enc2 y → x = y)
    (pk1 : PK₁) (pk2 : PK₂) (msg : List UInt8)
    (hsig : HybridWireSig Sig₁ PK₂ Sig₂)
    (hAccept : verifyHybridPinnedSig S₁ S₂ enc1 enc2
      (computeHybridIdCommit (enc1 pk1) (enc2 pk2)) pk1 msg hsig = true) :
    let bound := buildHybridBoundMessage (computeHybridIdCommit (enc1 pk1) (enc2 pk2))
      (enc1 pk1) (enc2 pk2) msg
    (hsig.carriedPk2 = pk2 ∧ S₁.verify pk1 bound hsig.sig1 = true ∧
      S₂.verify pk2 bound hsig.sig2 = true) ∨
    Nonempty (HashCollisionWitness (cshake256Bytes hybridIdCustom)) := by
  simp only [verifyHybridPinnedSig, checkHybridPinning, Bool.and_eq_true, decide_eq_true_eq] at hAccept
  rcases hAccept with ⟨⟨hCommit, hOne⟩, hTwo⟩
  match computeHybridIdCommit_binds hCommit with
  | .inl ⟨_, hKey⟩ =>
    have hEq := hEnc2Inj hKey
    simp only [hEq] at hOne hTwo
    exact .inl ⟨hEq, hOne, hTwo⟩
  | .inr col => exact .inr ⟨col⟩

/-- Changing a partner key cannot preserve the signed envelope, even before hashing. -/
theorem hybrid_partner_substitution_rejected (id pk pq pq' msg : List UInt8)
    (hne : pq ≠ pq') :
    buildHybridBoundMessage id pk pq msg ≠ buildHybridBoundMessage id pk pq' msg :=
  fun h => hne (hybrid_bound_message_injective h).2.2.1

/-- A component which rejects the framed message cannot be smuggled through as a raw-message signature. -/
theorem hybrid_raw_signature_rejected {PK₁ SK₁ Sig₁ PK₂ SK₂ Sig₂ : Type}
    (S₁ : AbstractSigScheme PK₁ SK₁ (List UInt8) Sig₁)
    (S₂ : AbstractSigScheme PK₂ SK₂ (List UInt8) Sig₂)
    (enc1 : PK₁ → List UInt8) (enc2 : PK₂ → List UInt8)
    (id : List UInt8) (pk : PK₁) (msg : List UInt8) (sig : HybridWireSig Sig₁ PK₂ Sig₂)
    (h : S₁.verify pk (buildHybridBoundMessage id (enc1 pk) (enc2 sig.carriedPk2) msg) sig.sig1 = false) :
    verifyHybridPinnedSig S₁ S₂ enc1 enc2 id pk msg sig = false := by
  simp only [verifyHybridPinnedSig, h, Bool.and_false, Bool.false_and]

/-! ### Tri-State Wire Verifier (`VerifyReply` & `verifyWire_malformed_iff`) -/

inductive FaultStage where
  | headerMagicOrVersion | publicKeyLength | signatureFraming | layerCountMismatch
  deriving DecidableEq, Repr

/-- Tri-state verification reply (`VerifyReply`): never conflates `.wireMalformed` with `.reject`. -/
inductive VerifyReply where
  | accept | reject | wireMalformed (stage : FaultStage)
  deriving DecidableEq, Repr

/-- Canonical standalone wire magic `"QSAG\x01"` (`[0x51, 0x53, 0x41, 0x47, 0x01]`). -/
def pqWireMagic : List UInt8 := [0x51, 0x53, 0x41, 0x47, 0x01]

def encodePublicKeyWire (pk : PqPublicKey) : List UInt8 := pk.pkSeed ++ pk.pkRoot

def parsePublicKeyWire (rawPk : List UInt8) : Sum FaultStage PqPublicKey :=
  if rawPk.length ≠ 64 then .inl .publicKeyLength
  else .inr { pkSeed := rawPk.take 32, pkRoot := rawPk.drop 32 }

def checkLayerSigFraming (params : PqHashParams) (ls : LayerXmssSig) : Bool :=
  decide (ls.wotsChains.length = params.ell1) && ls.wotsChains.all (fun c => decide (c.length = 32)) &&
  decide (ls.authPath.length = params.subtreeHeight) && ls.authPath.all (fun s => decide (s.length = 32))

def checkForsOpeningFraming (params : PqHashParams) (op : ForsTreeOpening) : Bool :=
  decide (op.secretVal.length = 32) && decide (op.authPath.length = params.forsHeight) &&
  op.authPath.all (fun s => decide (s.length = 32))

def checkWireHeaderAndLengths (params : PqHashParams) (rawPk : List UInt8)
    (magicPrefix : List UInt8) (sig : PqHashSig) : Option FaultStage :=
  if magicPrefix ≠ pqWireMagic then some .headerMagicOrVersion
  else if rawPk.length ≠ 64 then some .publicKeyLength
  else if sig.layerSigs.length ≠ params.numLayers then some .layerCountMismatch
  else if sig.rRand.length ≠ 32 ||
          !(if params.statefulJorts then sig.forsOpenings.isEmpty && decide (sig.msgTswCtr = 0)
            else decide (sig.forsOpenings.length = params.forsTrees) && sig.forsOpenings.all (checkForsOpeningFraming params)) ||
          !(sig.layerSigs.all (checkLayerSigFraming params)) then some .signatureFraming
  else none

/-- Tri-state wire verifier separating framing checks from cryptographic `verifyPqHashSig`. -/
@[expose] def verifyPqWireEnvelope (suite : TweakableHashSuite) (params : PqHashParams)
    (rawPk rawMsg magicPrefix : List UInt8) (sig : PqHashSig) : VerifyReply :=
  match checkWireHeaderAndLengths params rawPk magicPrefix sig with
  | some stage => .wireMalformed stage
  | none =>
    let pk : PqPublicKey := { pkSeed := rawPk.take 32, pkRoot := rawPk.drop 32 }
    if verifyPqHashSig suite params pk rawMsg sig then .accept else .reject

/-- **Tri-State Wire Verifier Characterization (`verifyWire_malformed_iff`)**. -/
theorem verifyWire_malformed_iff
    (suite : TweakableHashSuite) (params : PqHashParams)
    (rawPk rawMsg magicPrefix : List UInt8) (sig : PqHashSig) (stage : FaultStage) :
    (verifyPqWireEnvelope suite params rawPk rawMsg magicPrefix sig = .wireMalformed stage ↔
      checkWireHeaderAndLengths params rawPk magicPrefix sig = some stage) ∧
    (verifyPqWireEnvelope suite params rawPk rawMsg magicPrefix sig = .accept ↔
      checkWireHeaderAndLengths params rawPk magicPrefix sig = none ∧
      verifyPqHashSig suite params { pkSeed := rawPk.take 32, pkRoot := rawPk.drop 32 } rawMsg sig = true) ∧
    (verifyPqWireEnvelope suite params rawPk rawMsg magicPrefix sig = .reject ↔
      checkWireHeaderAndLengths params rawPk magicPrefix sig = none ∧
      verifyPqHashSig suite params { pkSeed := rawPk.take 32, pkRoot := rawPk.drop 32 } rawMsg sig = false) := by
  unfold verifyPqWireEnvelope
  cases hChk : checkWireHeaderAndLengths params rawPk magicPrefix sig with
  | some _ => simp
  | none =>
    cases hVer : verifyPqHashSig suite params { pkSeed := rawPk.take 32, pkRoot := rawPk.drop 32 } rawMsg sig <;>
      simp [hVer]

theorem thPreHash_eq (suite : TweakableHashSuite) (pkSeed pkRoot msg : List UInt8) :
    thPreHash suite pkSeed pkRoot msg = thCall suite tagHPre pkSeed zeroAdrs [pkRoot, msg] := by rfl

theorem thHashMsg_eq (suite : TweakableHashSuite) (rRand pkSeed pkRoot mu : List UInt8)
    (layerIdx : UInt32) (treeIdx : UInt64) (kpIdx : UInt32) (ctr : Nat) :
    thHashMsg suite rRand pkSeed pkRoot mu layerIdx treeIdx kpIdx ctr =
      thCall suite tagHMsg pkSeed ⟨layerIdx, treeIdx, .wotsHash, kpIdx, 0, UInt32.ofNat ctr⟩ [rRand, pkRoot, mu, be 4 ctr] ++
      thCall suite tagHMsg pkSeed ⟨layerIdx, treeIdx, .wotsHash, kpIdx, 1, UInt32.ofNat ctr⟩ [rRand, pkRoot, mu, be 4 ctr] := by rfl

theorem thTweakTl_eq (suite : TweakableHashSuite) (pkSeed : List UInt8) (adrs : HashAdrs) (limbs : List (List UInt8)) :
    thTweakTl suite pkSeed adrs limbs = thCall suite tagThTl pkSeed adrs limbs := by rfl

theorem forsLeafHashFromSecret_eq (suite : TweakableHashSuite) (pkSeed : List UInt8)
    (treeIdx : UInt64) (kpIdx globalForsLeaf : Nat) (secVal : List UInt8) :
    forsLeafHashFromSecret suite pkSeed treeIdx kpIdx globalForsLeaf secVal =
      thChainF suite pkSeed ⟨0, treeIdx, .forsTree, UInt32.ofNat kpIdx, 0, UInt32.ofNat globalForsLeaf⟩ secVal := by rfl

theorem recoverWotsEndpoints_eq (suite : TweakableHashSuite) (params : PqHashParams) (pkSeed : List UInt8)
    (layer : UInt32) (tree : UInt64) (kp : Nat) (digits : List Nat) (sigChains : List (List UInt8)) :
    recoverWotsEndpoints suite params pkSeed layer tree kp digits sigChains =
      (List.range params.ell1).map fun r =>
        wotsChainSteps suite pkSeed layer tree kp r (digits.getD r 0) ((params.w - 1) - digits.getD r 0) (sigChains.getD r []) := by rfl

theorem recoverWotsPkFromSig_eq (suite : TweakableHashSuite) (params : PqHashParams) (pkSeed : List UInt8)
    (layer : UInt32) (tree : UInt64) (kp : Nat) (digits : List Nat) (sigChains : List (List UInt8)) :
    recoverWotsPkFromSig suite params pkSeed layer tree kp digits sigChains =
      thTweakTl suite pkSeed ⟨layer, tree, .wotsPk, UInt32.ofNat kp, 0, 0⟩
        (recoverWotsEndpoints suite params pkSeed layer tree kp digits sigChains) := by rfl

theorem recoverForsTreeRoots_zero (suite : TweakableHashSuite) (params : PqHashParams)
    (pkSeed : List UInt8) (treeIdx : UInt64) (kpIdx : Nat)
    (idxs : List Nat) (openings : List ForsTreeOpening) (j : Nat) :
    recoverForsTreeRoots suite params pkSeed treeIdx kpIdx idxs openings j 0 = some [] := by rfl

theorem recoverForsTreeRoots_succ (suite : TweakableHashSuite) (params : PqHashParams)
    (pkSeed : List UInt8) (treeIdx : UInt64) (kpIdx : Nat)
    (idxs : List Nat) (openings : List ForsTreeOpening) (j rem : Nat) :
    recoverForsTreeRoots suite params pkSeed treeIdx kpIdx idxs openings j (rem + 1) =
      let idxJ := idxs.getD j 0
      let op := openings.getD j ⟨[], []⟩
      let globalU := j * (2 ^ params.forsHeight) + idxJ
      let leafH := forsLeafHashFromSecret suite pkSeed treeIdx kpIdx globalU op.secretVal
      match walkMerkleAuthPath suite pkSeed 0 treeIdx .forsTree params.forsHeight j idxJ leafH op.authPath with
      | none => none
      | some rJ =>
        match recoverForsTreeRoots suite params pkSeed treeIdx kpIdx idxs openings (j + 1) rem with
        | none => none
        | some rs => some (rJ :: rs) := by rfl

theorem recoverForsPk_eq (suite : TweakableHashSuite) (params : PqHashParams)
    (pkSeed : List UInt8) (treeIdx : UInt64) (kpIdx : Nat)
    (hmsg : List UInt8) (openings : List ForsTreeOpening) :
    recoverForsPk suite params pkSeed treeIdx kpIdx hmsg openings =
      if openings.length ≠ params.forsTrees then none
      else
        let idxs := deriveForsIndices params.forsTrees params.forsHeight hmsg
        match recoverForsTreeRoots suite params pkSeed treeIdx kpIdx idxs openings 0 params.forsTrees with
        | none => none
        | some roots =>
          some (thTweakTl suite pkSeed ⟨0, treeIdx, .forsRoots, UInt32.ofNat kpIdx, 0, 0⟩ roots) := by rfl

theorem verifyHypertreeLayers_nil (suite : TweakableHashSuite) (params : PqHashParams)
    (pkSeed pkRoot layer0Rand : List UInt8) (layerIdx globalIdx : Nat) (curRoot : List UInt8) :
    verifyHypertreeLayers suite params pkSeed pkRoot layer0Rand layerIdx globalIdx curRoot [] = some curRoot := by rfl

theorem verifyHypertreeLayers_cons (suite : TweakableHashSuite) (params : PqHashParams)
    (pkSeed pkRoot layer0Rand : List UInt8) (layerIdx globalIdx : Nat) (curRoot : List UInt8)
    (lsig : LayerXmssSig) (rest : List LayerXmssSig) :
    verifyHypertreeLayers suite params pkSeed pkRoot layer0Rand layerIdx globalIdx curRoot (lsig :: rest) =
      let subLeaves := 2 ^ params.subtreeHeight
      let kpIdx := globalIdx % subLeaves
      let kpU32 := UInt32.ofNat kpIdx
      let treeIdxNat := globalIdx / subLeaves
      let treeIdx := UInt64.ofNat treeIdxNat
      let layerU32 := UInt32.ofNat layerIdx
      let hmsg := thHashMsg suite layer0Rand pkSeed pkRoot curRoot layerU32 treeIdx kpU32 lsig.tswCtr
      let digits := extractBaseWDigits params.w params.ell1 hmsg
      if !(checkTargetSum params.w params.ell1 params.targetSum digits) then none
      else if lsig.wotsChains.length ≠ params.ell1 then none
      else
        let wotsPk := recoverWotsPkFromSig suite params pkSeed layerU32 treeIdx kpIdx digits lsig.wotsChains
        match walkMerkleAuthPath suite pkSeed layerU32 treeIdx .tree params.subtreeHeight 0 kpIdx wotsPk lsig.authPath with
        | none => none
        | some nextSubtreeRoot =>
          verifyHypertreeLayers suite params pkSeed pkRoot [] (layerIdx + 1) treeIdxNat nextSubtreeRoot rest := by rfl

theorem sumDigits_nil : sumDigits [] = 0 := by rfl
theorem sumDigits_cons (d : Nat) (ds : List Nat) : sumDigits (d :: ds) = d + sumDigits ds := by rfl

theorem PqHashParams.targetSum_eq (p : PqHashParams) :
    p.targetSum = (p.ell1 * (p.w - 1)) / 2 := by rfl

theorem PqHashParams.wellFormed_eq (p : PqHashParams) :
    p.wellFormed =
      (decide (0 < p.numLayers) && decide (2 ≤ p.w) && decide (p.w ≤ 256) &&
       decide (0 < p.ell1) && decide (p.ell1 ≤ 256) &&
       decide (p.subtreeHeight ≤ 30) && decide (p.forsHeight ≤ 30) &&
       decide ((p.numLayers - 1) * p.subtreeHeight ≤ 64) &&
       decide (p.numLayers * p.subtreeHeight ≤ 62) &&
       (p.statefulJorts || (decide (0 < p.forsTrees) && decide (88 + p.forsTrees * p.forsHeight ≤ 512)))) := by rfl

theorem extractBaseWDigits_eq (w ell1 : Nat) (digestBytes : List UInt8) :
    extractBaseWDigits w ell1 digestBytes =
      let wSafe := if w < 2 then 4 else w
      (List.range ell1).map fun idx =>
        if wSafe = 4 then
          let byteIdx := idx / 4
          let shift := (3 - (idx % 4)) * 2
          let b := (digestBytes.getD byteIdx 0).toNat
          (b / (2 ^ shift)) % 4
        else
          let lgW := Nat.log2 wSafe
          let perByte := 8 / lgW
          let byteIdx := idx / perByte
          let shift := (perByte - 1 - idx % perByte) * lgW
          ((digestBytes.getD byteIdx 0).toNat / 2 ^ shift) % wSafe := by rfl

/-! ## Checked compatibility shims (`ThresholdMpc` / `Aggregation` cross-lane bridge)

`evalStatelessCheckedSign` / `verifyStatelessChecked` are retained as backward-compatible shims for
active callers in `ThresholdMpc.lean`. Section 6 immediately below provides the complete byte-exact
production Rust (`crates/qsag-core/src/tsw_baggy.rs`) signer, verifier, FORS recovery, `H_INTERNAL`
upper-layer / stateless FORS-root hashing, explicit-`keyPair` Merkle trees, and canonical wire codec
(`evalProductionStatelessSign`, `evalProductionStatefulSign`, `verifyProductionPqHashSig`,
`encodeProductionSigWire`, `decodeProductionSigWire`). -/

/-- Parameter test under which `extractBaseWDigitsChecked` succeeds on every 64-byte digest. -/
def PqHashParams.checkedDigitGeometry (p : PqHashParams) : Bool :=
  decide (2 ≤ p.w) && decide (p.w ≤ 256) && decide (2 ^ Nat.log2 p.w = p.w) &&
  decide (p.ell1 ≤ 64 * (8 / Nat.log2 p.w))

theorem PqHashParams.checkedDigitGeometry_eq (p : PqHashParams) :
    p.checkedDigitGeometry =
      (decide (2 ≤ p.w) && decide (p.w ≤ 256) && decide (2 ^ Nat.log2 p.w = p.w) &&
       decide (p.ell1 ≤ 64 * (8 / Nat.log2 p.w))) := by rfl

/-- Under the geometry test the unchecked extraction used by the signing core is exactly the
    successful output of the checked extraction. -/
theorem extractBaseWDigitsChecked_of_geometry (p : PqHashParams)
    (hGeom : p.checkedDigitGeometry = true) (bytes : List UInt8) (hLen : bytes.length = 64) :
    extractBaseWDigitsChecked p.w p.ell1 bytes = some (extractBaseWDigits p.w p.ell1 bytes) := by
  rw [PqHashParams.checkedDigitGeometry_eq] at hGeom
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hGeom
  obtain ⟨⟨⟨h2, h256⟩, hPow⟩, hEll⟩ := hGeom
  unfold extractBaseWDigitsChecked
  rw [hLen]
  simp only [h2, h256, hPow, hEll, and_self, ↓reduceIte]

/-- Regression: a radix that is not a power of two fails the geometry test. -/
theorem checkedDigitGeometry_rejects_radix_three :
    (⟨3, 8, 2, 2, 4, 2, 4, false⟩ : PqHashParams).checkedDigitGeometry = false := by
  decide +kernel

/-- Regression: more digits than the 64-byte digest holds fails the geometry test. -/
theorem checkedDigitGeometry_rejects_overlong :
    (⟨16, 129, 2, 2, 4, 2, 4, false⟩ : PqHashParams).checkedDigitGeometry = false := by
  decide +kernel

theorem corduroyCustody128_checkedDigitGeometry :
    corduroyCustody128Params.checkedDigitGeometry = true := by decide +kernel

/-- Every accepted counter found by the grinder carries digits that the checked extraction
    returns for its digest. -/
theorem grindTswCounterAux_checked {suite : TweakableHashSuite} {p : PqHashParams}
    (hGeom : p.checkedDigitGeometry = true)
    {rRand pkSeed pkRoot mu : List UInt8} {layerIdx : UInt32} {treeIdx : UInt64} {kpIdx : UInt32}
    {curCtr fuel ctr : Nat} {digits : List Nat} {hmsg : List UInt8}
    (h : grindTswCounterAux suite p.w p.ell1 p.targetSum rRand pkSeed pkRoot mu layerIdx treeIdx
          kpIdx curCtr fuel = some (ctr, digits, hmsg)) :
    extractBaseWDigitsChecked p.w p.ell1 hmsg = some digits := by
  obtain ⟨hm, hd, _⟩ := grindTswCounterAux_sound h
  rw [hd]
  exact extractBaseWDigitsChecked_of_geometry p hGeom hmsg
    (hm ▸ thHashMsg_length _ _ _ _ _ _ _ _ _)

/-- Shape of a successful stateless `evalSingleSign` call. -/
theorem evalSingleSign_stateless_inv (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (msg optRand : List UInt8) (leaf maxGrind : Nat) (sig : PqHashSig)
    (hMode : params.statefulJorts = false)
    (h : evalSingleSign suite params sk msg optRand leaf maxGrind = some sig) :
    params.wellFormed = true ∧ leaf < 2 ^ (params.numLayers * params.subtreeHeight) ∧
    sig.rRand = thPrfMsg suite sk.skPrf optRand
      (thPreHash suite sk.pkSeed (derivePublicKey suite params sk).pkRoot msg) ∧
    sig.leafGlobalIdx = leaf ∧
    (∃ dg hmsg0,
      grindTswCounterAux suite params.w params.ell1 params.targetSum
        (thPrfMsg suite sk.skPrf optRand
          (thPreHash suite sk.pkSeed (derivePublicKey suite params sk).pkRoot msg))
        sk.pkSeed (derivePublicKey suite params sk).pkRoot
        (thPreHash suite sk.pkSeed (derivePublicKey suite params sk).pkRoot msg)
        0 (UInt64.ofNat (leaf / 2 ^ params.subtreeHeight))
        (UInt32.ofNat (leaf % 2 ^ params.subtreeHeight)) 0 maxGrind =
          some (sig.msgTswCtr, dg, hmsg0) ∧
      sig.forsOpenings = buildForsOpenings suite params sk
        (UInt64.ofNat (leaf / 2 ^ params.subtreeHeight)) (leaf % 2 ^ params.subtreeHeight) hmsg0) ∧
    signHypertreeLayers suite params sk (derivePublicKey suite params sk).pkRoot [] maxGrind 0 leaf
      (computeForsPk suite params sk (UInt64.ofNat (leaf / 2 ^ params.subtreeHeight))
        (leaf % 2 ^ params.subtreeHeight)) params.numLayers = some sig.layerSigs := by
  unfold evalSingleSign at h
  cases hWf : params.wellFormed
  · simp [hWf] at h
  · cases hLeaf : decide (leaf < 2 ^ (params.numLayers * params.subtreeHeight))
    · simp [hWf, hLeaf] at h
    · simp only [hWf, hLeaf, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hMode] at h
      split at h
      · cases h
      · rename_i ctr0 dg hmsg0 hG
        split at h
        · cases h
        · rename_i layerSigs hLs
          simp only [Option.some.injEq] at h
          subst h
          exact ⟨rfl, of_decide_eq_true hLeaf, rfl, rfl, ⟨dg, hmsg0, hG, rfl⟩, hLs⟩

/-- Stateless signer with the HXOF-derived hypertree leaf and checked digit geometry. -/
def evalStatelessCheckedSign (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (msg optRand : List UInt8) (maxGrind : Nat) : Option PqHashSig :=
  if !params.checkedDigitGeometry then none
  else
    let pk := derivePublicKey suite params sk
    let mu := thPreHash suite pk.pkSeed pk.pkRoot msg
    let rRand := thPrfMsg suite sk.skPrf optRand mu
    match deriveStatelessInputs suite params rRand pk.pkSeed pk.pkRoot mu with
    | none => none
    | some (leaf, _) => evalSingleSign suite params sk msg optRand leaf maxGrind

theorem evalStatelessCheckedSign_eq (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (msg optRand : List UInt8) (maxGrind : Nat) :
    evalStatelessCheckedSign suite params sk msg optRand maxGrind =
      if !params.checkedDigitGeometry then none
      else
        match deriveStatelessInputs suite params
            (thPrfMsg suite sk.skPrf optRand
              (thPreHash suite sk.pkSeed (derivePublicKey suite params sk).pkRoot msg))
            sk.pkSeed (derivePublicKey suite params sk).pkRoot
            (thPreHash suite sk.pkSeed (derivePublicKey suite params sk).pkRoot msg) with
        | none => none
        | some (leaf, _) => evalSingleSign suite params sk msg optRand leaf maxGrind := by rfl

/-- Verifier that recomputes the HXOF-derived leaf from `(R, mu)` and rejects any other leaf,
    any stateful profile, and any parameter set failing the digit-geometry test. -/
def verifyStatelessChecked (suite : TweakableHashSuite) (params : PqHashParams)
    (pk : PqPublicKey) (msg : List UInt8) (sig : PqHashSig) : Bool :=
  params.checkedDigitGeometry &&
  (match deriveStatelessInputs suite params sig.rRand pk.pkSeed pk.pkRoot
      (thPreHash suite pk.pkSeed pk.pkRoot msg) with
   | none => false
   | some (leaf, _) => decide (sig.leafGlobalIdx = leaf)) &&
  verifyPqHashSig suite params pk msg sig

theorem verifyStatelessChecked_eq (suite : TweakableHashSuite) (params : PqHashParams)
    (pk : PqPublicKey) (msg : List UInt8) (sig : PqHashSig) :
    verifyStatelessChecked suite params pk msg sig =
      (params.checkedDigitGeometry &&
      (match deriveStatelessInputs suite params sig.rRand pk.pkSeed pk.pkRoot
          (thPreHash suite pk.pkSeed pk.pkRoot msg) with
       | none => false
       | some (leaf, _) => decide (sig.leafGlobalIdx = leaf)) &&
      verifyPqHashSig suite params pk msg sig) := by rfl

/-- The checked verifier implies the legacy verifier, the geometry test, and the leaf binding. -/
theorem verifyStatelessChecked_sound (suite : TweakableHashSuite) (params : PqHashParams)
    (pk : PqPublicKey) (msg : List UInt8) (sig : PqHashSig)
    (h : verifyStatelessChecked suite params pk msg sig = true) :
    params.checkedDigitGeometry = true ∧ params.statefulJorts = false ∧
    verifyPqHashSig suite params pk msg sig = true ∧
    ∃ idxs, deriveStatelessInputs suite params sig.rRand pk.pkSeed pk.pkRoot
      (thPreHash suite pk.pkSeed pk.pkRoot msg) = some (sig.leafGlobalIdx, idxs) := by
  rw [verifyStatelessChecked_eq] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hGeom, hLeaf⟩, hVer⟩ := h
  cases hD : deriveStatelessInputs suite params sig.rRand pk.pkSeed pk.pkRoot
      (thPreHash suite pk.pkSeed pk.pkRoot msg) with
  | none => rw [hD] at hLeaf; cases hLeaf
  | some pr =>
    rcases pr with ⟨leaf, idxs⟩
    rw [hD] at hLeaf
    have hEq : sig.leafGlobalIdx = leaf := of_decide_eq_true hLeaf
    refine ⟨hGeom, ?_, hVer, idxs, by rw [hEq]⟩
    cases hSt : params.statefulJorts
    · rfl
    · rw [stateless_inputs_reject_stateful suite params _ _ _ _ hSt] at hD
      cases hD

/-- Completeness of the checked pair. -/
theorem verifyStatelessChecked_evalStatelessCheckedSign (suite : TweakableHashSuite)
    (params : PqHashParams) (sk : PqSecretKey) (msg optRand : List UInt8) (maxGrind : Nat)
    (sig : PqHashSig)
    (hSign : evalStatelessCheckedSign suite params sk msg optRand maxGrind = some sig) :
    verifyStatelessChecked suite params (derivePublicKey suite params sk) msg sig = true := by
  rw [evalStatelessCheckedSign_eq] at hSign
  cases hGeom : params.checkedDigitGeometry
  · simp [hGeom] at hSign
  · simp only [hGeom, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hSign
    cases hD : deriveStatelessInputs suite params
        (thPrfMsg suite sk.skPrf optRand
          (thPreHash suite sk.pkSeed (derivePublicKey suite params sk).pkRoot msg))
        sk.pkSeed (derivePublicKey suite params sk).pkRoot
        (thPreHash suite sk.pkSeed (derivePublicKey suite params sk).pkRoot msg) with
    | none => rw [hD] at hSign; cases hSign
    | some pr =>
      rcases pr with ⟨leaf, idxs⟩
      rw [hD] at hSign
      have hSt : params.statefulJorts = false := by
        cases hSt : params.statefulJorts
        · rfl
        · rw [stateless_inputs_reject_stateful suite params _ _ _ _ hSt] at hD
          cases hD
      obtain ⟨_, _, hR, hL, _, _⟩ :=
        evalSingleSign_stateless_inv suite params sk msg optRand leaf maxGrind sig hSt hSign
      have hVer := verifyPqHashSig_evalSingleSign suite params sk msg optRand leaf maxGrind sig hSign
      rw [verifyStatelessChecked_eq, hGeom, hVer, hR]
      have hD' : deriveStatelessInputs suite params
          (thPrfMsg suite sk.skPrf optRand
            (thPreHash suite sk.pkSeed (derivePublicKey suite params sk).pkRoot msg))
          (derivePublicKey suite params sk).pkSeed (derivePublicKey suite params sk).pkRoot
          (thPreHash suite (derivePublicKey suite params sk).pkSeed
            (derivePublicKey suite params sk).pkRoot msg) = some (leaf, idxs) := hD
      rw [hD']
      simp [hL]

/-- Regression: a signature relocated to any leaf other than the HXOF-derived one is rejected,
    whatever the legacy verifier says about it. -/
theorem verifyStatelessChecked_rejects_wrong_leaf (suite : TweakableHashSuite)
    (params : PqHashParams) (pk : PqPublicKey) (msg : List UInt8) (sig : PqHashSig)
    (leaf : Nat) (idxs : List Nat)
    (hD : deriveStatelessInputs suite params sig.rRand pk.pkSeed pk.pkRoot
      (thPreHash suite pk.pkSeed pk.pkRoot msg) = some (leaf, idxs))
    (hNe : sig.leafGlobalIdx ≠ leaf) :
    verifyStatelessChecked suite params pk msg sig = false := by
  rw [verifyStatelessChecked_eq, hD]
  simp [hNe]

/-- Regression: a stateful profile never passes the checked stateless verifier. -/
theorem verifyStatelessChecked_rejects_stateful (suite : TweakableHashSuite)
    (params : PqHashParams) (pk : PqPublicKey) (msg : List UInt8) (sig : PqHashSig)
    (hSt : params.statefulJorts = true) :
    verifyStatelessChecked suite params pk msg sig = false := by
  rw [verifyStatelessChecked_eq, stateless_inputs_reject_stateful suite params _ _ _ _ hSt]
  simp

/-- All-zero toy suite used only to show that hypotheses below are jointly satisfiable. -/
def zeroToySuite : TweakableHashSuite where
  suiteId := []
  rawHash := fun _ => List.replicate 32 0
  rawHash_len := fun _ => List.length_replicate

/-- Toy profile whose target sum is met by the all-zero digest. -/
def zeroToyParams : PqHashParams := ⟨2, 1, 1, 1, 1, 1, 1, false⟩

/-! ## 6. Production Rust-Aligned Hypertree & FORS Core (`crates/qsag-core/src/tsw_baggy.rs`)

Byte-exact Lean specification and completeness/soundness proofs matching `crates/qsag-core/src/tsw_baggy.rs`:
1. Exact parameter & preset manifest (`productionWellFormed`, `productionLeafIdxInRange`, `wireSigBytes`).
2. MSB-first bitstream `extractBaseWBitstream` / `extractBaseWBitstreamChecked` alongside `extractBaseWDigitsChecked`.
3. Explicit leaf-message (`thHashLeafMsg`, `TAG_H_MSG`) vs internal-node / stateless FORS-root
   (`thHashInternalNode`, `TAG_H_INTERNAL`, zero `rRand` dependence) `TSW` hashing and counter grinding.
4. Explicit-`keyPair` Merkle subtree builder/walker (`computeMerkleNodeKp`, `buildMerkleAuthPathKp`,
   `walkMerkleAuthPathKp`) binding `kp0` on `.forsTree` internal nodes and `0` on `.tree` nodes.
5. `(j, u)`-indexed FORS secret/leaf addressing (`forsIndexedSecretLeaf`, `forsIndexedLeafHash`) with
   XOF-derived `deriveProductionStatelessInputs` `(leafGlobalIdx, idxs)` threaded end-to-end into
   signing (`evalProductionStatelessSign`) and verification (`verifyProductionPqHashSig`).
6. Exact `PQ_WIRE_MAGIC` fixed-layout wire codec (`encodeProductionSigWire` / `decodeProductionSigWire`)
   with proved round-trip identity. -/

theorem PqHashParams.productionWellFormed_eq (p : PqHashParams) :
    p.productionWellFormed =
      (decide (0 < p.numLayers) &&
       decide (2 ≤ p.w) && decide (p.w ≤ 256) && decide (2 ^ Nat.log2 p.w = p.w) &&
       decide (p.ell1 * Nat.log2 p.w = 256) &&
       decide (0 < p.subtreeHeight) && decide (p.subtreeHeight ≤ 30) &&
       decide (p.forsHeight ≤ 30) &&
       decide (0 < p.numLayers * p.subtreeHeight) &&
       decide (p.numLayers * p.subtreeHeight ≤ 62) &&
       decide (0 < p.maxSigsLog2) &&
       decide (p.maxSigsLog2 ≤ p.numLayers * p.subtreeHeight) &&
       (if p.statefulJorts then decide (p.forsTrees = 0) && decide (p.forsHeight = 0)
        else decide (0 < p.forsTrees) && decide (0 < p.forsHeight))) := by rfl

theorem PqHashParams.productionLeafIdxInRange_eq (p : PqHashParams) (leafGlobalIdx : Nat) :
    p.productionLeafIdxInRange leafGlobalIdx =
      (let totalBits := p.numLayers * p.subtreeHeight
       let capBits := if p.statefulJorts && decide (p.maxSigsLog2 < totalBits) then p.maxSigsLog2 else totalBits
       decide (leafGlobalIdx < 2 ^ capBits)) := by rfl

theorem PqHashParams.wireSigBytes_eq (p : PqHashParams) :
    p.wireSigBytes =
      (let forsBytes := if p.statefulJorts then 0 else p.forsTrees * (32 + p.forsHeight * 32)
       49 + forsBytes + p.numLayers * (4 + p.ell1 * 32 + p.subtreeHeight * 32)) := by rfl

theorem corduroyCustody128_productionWellFormed :
    corduroyCustody128Params.productionWellFormed = true := by decide +kernel
theorem baggy128f_productionWellFormed :
    baggy128fParams.productionWellFormed = true := by decide +kernel
theorem jortsPoseidon2_productionWellFormed :
    jortsPoseidon2Params.productionWellFormed = true := by decide +kernel
theorem jortsBenchCached_productionWellFormed :
    jortsBenchCachedParams.productionWellFormed = true := by decide +kernel
theorem compactGolden_productionWellFormed :
    compactGoldenParams.productionWellFormed = true := by decide +kernel
theorem compactJortsProd_productionWellFormed :
    compactJortsProdParams.productionWellFormed = true := by decide +kernel

theorem PqHashParams.productionWellFormed_w_ell1 (p : PqHashParams)
    (h : p.productionWellFormed = true) :
    (p.w = 2 ∧ p.ell1 = 256) ∨ (p.w = 4 ∧ p.ell1 = 128) ∨
    (p.w = 16 ∧ p.ell1 = 64) ∨ (p.w = 256 ∧ p.ell1 = 32) := by
  rw [PqHashParams.productionWellFormed_eq] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h
  rcases h with ⟨_, h2, h256, hPow, hBits, _, _, _, _, _, _, _, _⟩
  match hLg : Nat.log2 p.w with
  | 0 => rw [hLg] at hPow; omega
  | 1 => rw [hLg] at hPow hBits; exact .inl ⟨hPow.symm, by omega⟩
  | 2 => rw [hLg] at hPow hBits; exact .inr (.inl ⟨hPow.symm, by omega⟩)
  | 3 => rw [hLg] at hBits; omega
  | 4 => rw [hLg] at hPow hBits; exact .inr (.inr (.inl ⟨hPow.symm, by omega⟩))
  | 5 => rw [hLg] at hBits; omega
  | 6 => rw [hLg] at hBits; omega
  | 7 => rw [hLg] at hBits; omega
  | 8 => rw [hLg] at hPow hBits; exact .inr (.inr (.inr ⟨hPow.symm, by omega⟩))
  | n + 9 =>
    have hPow9 : 2 ^ 9 ≤ 2 ^ p.w.log2 := Nat.pow_le_pow_right (by decide) (by omega)
    rw [hPow] at hPow9
    omega

theorem PqHashParams.productionWellFormed_facts (p : PqHashParams)
    (h : p.productionWellFormed = true) :
    0 < p.numLayers ∧ 2 ≤ p.w ∧ p.w ≤ 256 ∧ 2 ^ Nat.log2 p.w = p.w ∧
    p.ell1 * Nat.log2 p.w = 256 ∧ 0 < p.subtreeHeight ∧ p.subtreeHeight ≤ 30 ∧
    p.forsHeight ≤ 30 ∧ 0 < p.numLayers * p.subtreeHeight ∧
    p.numLayers * p.subtreeHeight ≤ 62 ∧ 0 < p.maxSigsLog2 ∧
    p.maxSigsLog2 ≤ p.numLayers * p.subtreeHeight ∧
    p.ell1 ≤ 32 * (8 / Nat.log2 p.w) ∧ p.numLayers ≤ 62 := by
  have hCases := p.productionWellFormed_w_ell1 h
  rw [PqHashParams.productionWellFormed_eq] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h
  rcases h with ⟨hD, h2, h256, hPow, hBits, hSubPos, hSubLe, hForsLe, hTotPos, hTotLe, hMaxPos, hMaxLe, _⟩
  have hEll32 : p.ell1 ≤ 32 * (8 / Nat.log2 p.w) := by
    rcases hCases with ⟨hw, hell⟩ | ⟨hw, hell⟩ | ⟨hw, hell⟩ | ⟨hw, hell⟩ <;> (rw [hw, hell]; decide)
  have hDLe62 : p.numLayers ≤ 62 := by
    have hMul : p.numLayers * 1 ≤ p.numLayers * p.subtreeHeight :=
      Nat.mul_le_mul_left p.numLayers hSubPos
    omega
  exact ⟨hD, h2, h256, hPow, hBits, hSubPos, hSubLe, hForsLe, hTotPos, hTotLe,
         hMaxPos, hMaxLe, hEll32, hDLe62⟩

theorem extractBaseWDigitsChecked_of_productionWellFormed (p : PqHashParams)
    (hWf : p.productionWellFormed = true) (bytes : List UInt8) (hLen : bytes.length = 32) :
    extractBaseWDigitsChecked p.w p.ell1 bytes = some (extractBaseWDigits p.w p.ell1 bytes) := by
  obtain ⟨_, h2, h256, hPow, _, _, _, _, _, _, _, _, hEll32, _⟩ := p.productionWellFormed_facts hWf
  unfold extractBaseWDigitsChecked
  rw [hLen]
  simp only [h2, h256, hPow, hEll32, and_self, ↓reduceIte]

/-- MSB-first bitstream base-`w` extractor across all power-of-two `w ∈ {2, 4, 8, 16, 32, 64, 128, 256}`,
    matching Rust `extract_base_w_digits_checked` without byte-local truncation. -/
def extractBaseWBitstream (w ell1 : Nat) (digestBytes : List UInt8) : List Nat :=
  let wSafe := if w < 2 then 4 else w
  let lgW := Nat.log2 wSafe
  (List.range ell1).map fun idx => extractBitWindow digestBytes (idx * lgW) lgW

def extractBaseWBitstreamChecked (w ell1 : Nat) (bytes : List UInt8) : Option (List Nat) :=
  if 2 ≤ w ∧ w ≤ 256 ∧ 2 ^ Nat.log2 w = w ∧ ell1 * Nat.log2 w ≤ bytes.length * 8 then
    some (extractBaseWBitstream w ell1 bytes)
  else none

theorem base8_msb_bitstream_digits :
    extractBaseWBitstreamChecked 8 2 [0xe0] = some [7, 0] ∧
    extractBaseWBitstreamChecked 8 5 [0x00, 0x00] = some [0, 0, 0, 0, 0] ∧
    extractBaseWBitstreamChecked 8 6 [0x00, 0x00] = none := by
  decide +kernel

/-- Production stateful leaf counter grinder (`thHashLeafMsg`, `32`-byte `H_MSG` digest, `curCtr < 2^32`). -/
def grindTswLeafCounterAux (suite : TweakableHashSuite) (w ell1 target : Nat)
    (rRand pkSeed pkRoot mu : List UInt8) (treeIdx : UInt64) (kpIdx : UInt32)
    (curCtr : Nat) : Nat → Option (Nat × List Nat × List UInt8)
  | 0 => none
  | fuel + 1 =>
    if !(decide (curCtr < 2 ^ 32)) then none
    else
      let hmsg := thHashLeafMsg suite rRand pkSeed pkRoot mu treeIdx kpIdx curCtr
      match extractBaseWDigitsChecked w ell1 hmsg with
      | none => none
      | some digits =>
        if checkTargetSum w ell1 target digits then
          some (curCtr, digits, hmsg)
        else
          grindTswLeafCounterAux suite w ell1 target rRand pkSeed pkRoot mu treeIdx kpIdx (curCtr + 1) fuel

/-- Production internal-node / stateless FORS-root counter grinder (`thHashInternalNode`, `32`-byte `H_INTERNAL`,
    zero `rRand` dependence, `curCtr < 2^32`). -/
def grindTswInternalCounterAux (suite : TweakableHashSuite) (w ell1 target : Nat)
    (pkSeed pkRoot nodeRoot : List UInt8) (layerIdx : UInt32) (treeIdx : UInt64) (kpIdx : UInt32)
    (curCtr : Nat) : Nat → Option (Nat × List Nat × List UInt8)
  | 0 => none
  | fuel + 1 =>
    if !(decide (curCtr < 2 ^ 32)) then none
    else
      let hmsg := thHashInternalNode suite pkSeed pkRoot nodeRoot layerIdx treeIdx kpIdx curCtr
      match extractBaseWDigitsChecked w ell1 hmsg with
      | none => none
      | some digits =>
        if checkTargetSum w ell1 target digits then
          some (curCtr, digits, hmsg)
        else
          grindTswInternalCounterAux suite w ell1 target pkSeed pkRoot nodeRoot layerIdx treeIdx kpIdx (curCtr + 1) fuel

theorem grindTswLeafCounterAux_zero (suite : TweakableHashSuite) (w ell1 target : Nat)
    (rRand pkSeed pkRoot mu : List UInt8) (treeIdx : UInt64) (kpIdx : UInt32) (curCtr : Nat) :
    grindTswLeafCounterAux suite w ell1 target rRand pkSeed pkRoot mu treeIdx kpIdx curCtr 0 =
      none := by rfl

theorem grindTswLeafCounterAux_succ (suite : TweakableHashSuite) (w ell1 target : Nat)
    (rRand pkSeed pkRoot mu : List UInt8) (treeIdx : UInt64) (kpIdx : UInt32) (curCtr fuel : Nat) :
    grindTswLeafCounterAux suite w ell1 target rRand pkSeed pkRoot mu treeIdx kpIdx curCtr
        (fuel + 1) =
      if !(decide (curCtr < 2 ^ 32)) then none
      else
        match extractBaseWDigitsChecked w ell1
            (thHashLeafMsg suite rRand pkSeed pkRoot mu treeIdx kpIdx curCtr) with
        | none => none
        | some digits =>
          if checkTargetSum w ell1 target digits then
            some (curCtr, digits, thHashLeafMsg suite rRand pkSeed pkRoot mu treeIdx kpIdx curCtr)
          else
            grindTswLeafCounterAux suite w ell1 target rRand pkSeed pkRoot mu treeIdx kpIdx
              (curCtr + 1) fuel := by rfl

theorem grindTswInternalCounterAux_zero (suite : TweakableHashSuite) (w ell1 target : Nat)
    (pkSeed pkRoot nodeRoot : List UInt8) (layerIdx : UInt32) (treeIdx : UInt64) (kpIdx : UInt32)
    (curCtr : Nat) :
    grindTswInternalCounterAux suite w ell1 target pkSeed pkRoot nodeRoot layerIdx treeIdx kpIdx
      curCtr 0 = none := by rfl

theorem grindTswInternalCounterAux_succ (suite : TweakableHashSuite) (w ell1 target : Nat)
    (pkSeed pkRoot nodeRoot : List UInt8) (layerIdx : UInt32) (treeIdx : UInt64) (kpIdx : UInt32)
    (curCtr fuel : Nat) :
    grindTswInternalCounterAux suite w ell1 target pkSeed pkRoot nodeRoot layerIdx treeIdx kpIdx
        curCtr (fuel + 1) =
      if !(decide (curCtr < 2 ^ 32)) then none
      else
        match extractBaseWDigitsChecked w ell1
            (thHashInternalNode suite pkSeed pkRoot nodeRoot layerIdx treeIdx kpIdx curCtr) with
        | none => none
        | some digits =>
          if checkTargetSum w ell1 target digits then
            some (curCtr, digits,
              thHashInternalNode suite pkSeed pkRoot nodeRoot layerIdx treeIdx kpIdx curCtr)
          else
            grindTswInternalCounterAux suite w ell1 target pkSeed pkRoot nodeRoot layerIdx treeIdx
              kpIdx (curCtr + 1) fuel := by rfl

theorem grindTswLeafCounterAux_sound {suite : TweakableHashSuite} {w ell1 target : Nat}
    {rRand pkSeed pkRoot mu : List UInt8} {treeIdx : UInt64} {kpIdx : UInt32}
    {curCtr fuel ctr : Nat} {digits : List Nat} {hmsg : List UInt8}
    (h : grindTswLeafCounterAux suite w ell1 target rRand pkSeed pkRoot mu treeIdx kpIdx curCtr fuel =
          some (ctr, digits, hmsg)) :
    ctr < 2 ^ 32 ∧
    hmsg = thHashLeafMsg suite rRand pkSeed pkRoot mu treeIdx kpIdx ctr ∧
    extractBaseWDigitsChecked w ell1 hmsg = some digits ∧
    checkTargetSum w ell1 target digits = true := by
  induction fuel generalizing curCtr with
  | zero => cases h
  | succ fuel ih =>
    unfold grindTswLeafCounterAux at h
    cases hLt : decide (curCtr < 2 ^ 32)
    · simp [hLt] at h
    · simp only [hLt, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
      cases hExt : extractBaseWDigitsChecked w ell1
          (thHashLeafMsg suite rRand pkSeed pkRoot mu treeIdx kpIdx curCtr) with
      | none => rw [hExt] at h; cases h
      | some dg =>
        rw [hExt] at h
        dsimp only at h
        cases hChk : checkTargetSum w ell1 target dg
        · rw [hChk] at h; simp only [Bool.false_eq_true, ↓reduceIte] at h; exact ih h
        · rw [hChk] at h; simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl, rfl⟩
          exact ⟨of_decide_eq_true hLt, rfl, hExt, hChk⟩

theorem grindTswInternalCounterAux_sound {suite : TweakableHashSuite} {w ell1 target : Nat}
    {pkSeed pkRoot nodeRoot : List UInt8} {layerIdx : UInt32} {treeIdx : UInt64} {kpIdx : UInt32}
    {curCtr fuel ctr : Nat} {digits : List Nat} {hmsg : List UInt8}
    (h : grindTswInternalCounterAux suite w ell1 target pkSeed pkRoot nodeRoot layerIdx treeIdx kpIdx curCtr fuel =
          some (ctr, digits, hmsg)) :
    ctr < 2 ^ 32 ∧
    hmsg = thHashInternalNode suite pkSeed pkRoot nodeRoot layerIdx treeIdx kpIdx ctr ∧
    extractBaseWDigitsChecked w ell1 hmsg = some digits ∧
    checkTargetSum w ell1 target digits = true := by
  induction fuel generalizing curCtr with
  | zero => cases h
  | succ fuel ih =>
    unfold grindTswInternalCounterAux at h
    cases hLt : decide (curCtr < 2 ^ 32)
    · simp [hLt] at h
    · simp only [hLt, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
      cases hExt : extractBaseWDigitsChecked w ell1
          (thHashInternalNode suite pkSeed pkRoot nodeRoot layerIdx treeIdx kpIdx curCtr) with
      | none => rw [hExt] at h; cases h
      | some dg =>
        rw [hExt] at h
        dsimp only at h
        cases hChk : checkTargetSum w ell1 target dg
        · rw [hChk] at h; simp only [Bool.false_eq_true, ↓reduceIte] at h; exact ih h
        · rw [hChk] at h; simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl, rfl⟩
          exact ⟨of_decide_eq_true hLt, rfl, hExt, hChk⟩

/-- Explicit-`keyPair` Merkle subtree evaluator matching `build_merkle_from_leaves_topdown`
    in `tsw_baggy.rs`: `nodeIdx` tracks the ADRS `hashStep` offset (starting at `j` for FORS tree `j`
    and `0` for XMSS), while `localBase` indexes the local leaf array `0 .. 2^h - 1`. -/
def computeMerkleNodeKp (suite : TweakableHashSuite) (pkSeed : List UInt8)
    (layer : UInt32) (tree : UInt64) (nodeKind : AdrsKind) (keyPair : UInt32)
    (leafFn : Nat → List UInt8) : Nat → Nat → Nat → List UInt8
  | 0, _, localBase => leafFn localBase
  | h + 1, nodeIdx, localBase =>
    let left  := computeMerkleNodeKp suite pkSeed layer tree nodeKind keyPair leafFn h (2 * nodeIdx) (2 * localBase)
    let right := computeMerkleNodeKp suite pkSeed layer tree nodeKind keyPair leafFn h (2 * nodeIdx + 1) (2 * localBase + 1)
    let adrs : HashAdrs := ⟨layer, tree, nodeKind, keyPair, UInt32.ofNat (h + 1), UInt32.ofNat nodeIdx⟩
    thNodeH suite pkSeed adrs left right

def buildMerkleAuthPathKp (suite : TweakableHashSuite) (pkSeed : List UInt8)
    (layer : UInt32) (tree : UInt64) (nodeKind : AdrsKind) (keyPair : UInt32)
    (leafFn : Nat → List UInt8) : Nat → Nat → Nat → Nat → List (List UInt8)
  | 0, _, _, _ => []
  | h + 1, nodeIdx, localBase, localIdx =>
    let half := 2 ^ h
    if localIdx < half then
      let sib := computeMerkleNodeKp suite pkSeed layer tree nodeKind keyPair leafFn h (2 * nodeIdx + 1) (2 * localBase + 1)
      sib :: buildMerkleAuthPathKp suite pkSeed layer tree nodeKind keyPair leafFn h (2 * nodeIdx) (2 * localBase) localIdx
    else
      let sib := computeMerkleNodeKp suite pkSeed layer tree nodeKind keyPair leafFn h (2 * nodeIdx) (2 * localBase)
      sib :: buildMerkleAuthPathKp suite pkSeed layer tree nodeKind keyPair leafFn h (2 * nodeIdx + 1) (2 * localBase + 1) (localIdx - half)

@[expose] def walkMerkleAuthPathKp (suite : TweakableHashSuite) (pkSeed : List UInt8)
    (layer : UInt32) (tree : UInt64) (nodeKind : AdrsKind) (keyPair : UInt32) :
    Nat → Nat → Nat → List UInt8 → List (List UInt8) → Option (List UInt8)
  | 0, _, _, leafHash, [] => some leafHash
  | 0, _, _, _, _ :: _ => none
  | _ + 1, _, _, _, [] => none
  | h + 1, nodeIdx, localIdx, leafHash, sib :: rest =>
    let half := 2 ^ h
    let adrs : HashAdrs := ⟨layer, tree, nodeKind, keyPair, UInt32.ofNat (h + 1), UInt32.ofNat nodeIdx⟩
    if localIdx < half then
      match walkMerkleAuthPathKp suite pkSeed layer tree nodeKind keyPair h (2 * nodeIdx) localIdx leafHash rest with
      | none => none
      | some sub => some (thNodeH suite pkSeed adrs sub sib)
    else
      match walkMerkleAuthPathKp suite pkSeed layer tree nodeKind keyPair h (2 * nodeIdx + 1) (localIdx - half) leafHash rest with
      | none => none
      | some sub => some (thNodeH suite pkSeed adrs sib sub)

theorem computeMerkleNodeKp_zero (suite : TweakableHashSuite) (pkSeed : List UInt8)
    (layer : UInt32) (tree : UInt64) (nodeKind : AdrsKind) (keyPair : UInt32)
    (leafFn : Nat → List UInt8) (nodeIdx localBase : Nat) :
    computeMerkleNodeKp suite pkSeed layer tree nodeKind keyPair leafFn 0 nodeIdx localBase =
      leafFn localBase := by rfl

theorem computeMerkleNodeKp_succ (suite : TweakableHashSuite) (pkSeed : List UInt8)
    (layer : UInt32) (tree : UInt64) (nodeKind : AdrsKind) (keyPair : UInt32)
    (leafFn : Nat → List UInt8) (h nodeIdx localBase : Nat) :
    computeMerkleNodeKp suite pkSeed layer tree nodeKind keyPair leafFn (h + 1) nodeIdx localBase =
      thNodeH suite pkSeed
        ⟨layer, tree, nodeKind, keyPair, UInt32.ofNat (h + 1), UInt32.ofNat nodeIdx⟩
        (computeMerkleNodeKp suite pkSeed layer tree nodeKind keyPair leafFn h (2 * nodeIdx)
          (2 * localBase))
        (computeMerkleNodeKp suite pkSeed layer tree nodeKind keyPair leafFn h (2 * nodeIdx + 1)
          (2 * localBase + 1)) := by rfl

theorem computeMerkleNodeKp_zero_eq (suite : TweakableHashSuite) (pkSeed : List UInt8)
    (layer : UInt32) (tree : UInt64) (nodeKind : AdrsKind) (leafFn : Nat → List UInt8) :
    ∀ (h nodeIdx : Nat),
      computeMerkleNodeKp suite pkSeed layer tree nodeKind 0 leafFn h nodeIdx nodeIdx =
        computeMerkleNode suite pkSeed layer tree nodeKind leafFn h nodeIdx
  | 0, _ => rfl
  | h + 1, nodeIdx => by
    simp only [computeMerkleNodeKp, computeMerkleNode,
      computeMerkleNodeKp_zero_eq suite pkSeed layer tree nodeKind leafFn h (2 * nodeIdx),
      computeMerkleNodeKp_zero_eq suite pkSeed layer tree nodeKind leafFn h (2 * nodeIdx + 1)]

theorem walkMerkleAuthPathKp_zero_eq (suite : TweakableHashSuite) (pkSeed : List UInt8)
    (layer : UInt32) (tree : UInt64) (nodeKind : AdrsKind) :
    ∀ (h nodeIdx localIdx : Nat) (leafHash : List UInt8) (path : List (List UInt8)),
      walkMerkleAuthPathKp suite pkSeed layer tree nodeKind 0 h nodeIdx localIdx leafHash path =
        walkMerkleAuthPath suite pkSeed layer tree nodeKind h nodeIdx localIdx leafHash path
  | 0, _, _, _, [] => rfl
  | 0, _, _, _, _ :: _ => rfl
  | _ + 1, _, _, _, [] => rfl
  | h + 1, nodeIdx, localIdx, leafHash, sib :: rest => by
    simp only [walkMerkleAuthPathKp, walkMerkleAuthPath]
    by_cases hHalf : localIdx < 2 ^ h
    · simp only [hHalf, ↓reduceIte,
        walkMerkleAuthPathKp_zero_eq suite pkSeed layer tree nodeKind h (2 * nodeIdx) localIdx leafHash rest]
    · simp only [hHalf, ↓reduceIte,
        walkMerkleAuthPathKp_zero_eq suite pkSeed layer tree nodeKind h (2 * nodeIdx + 1) (localIdx - 2 ^ h) leafHash rest]

theorem walkMerkleAuthPathKp_buildMerkleAuthPathKp
    (suite : TweakableHashSuite) (pkSeed : List UInt8)
    (layer : UInt32) (tree : UInt64) (nodeKind : AdrsKind) (keyPair : UInt32)
    (leafFn : Nat → List UInt8) :
    ∀ (h nodeIdx localBase localIdx : Nat), localIdx < 2 ^ h →
      walkMerkleAuthPathKp suite pkSeed layer tree nodeKind keyPair h nodeIdx localIdx
        (leafFn (localBase * (2 ^ h) + localIdx))
        (buildMerkleAuthPathKp suite pkSeed layer tree nodeKind keyPair leafFn h nodeIdx localBase localIdx) =
      some (computeMerkleNodeKp suite pkSeed layer tree nodeKind keyPair leafFn h nodeIdx localBase)
  | 0, _, localBase, localIdx, hLt => by
    have h0 : localIdx = 0 := by simp at hLt; exact hLt
    subst h0
    simp [buildMerkleAuthPathKp, walkMerkleAuthPathKp, computeMerkleNodeKp]
  | h + 1, nodeIdx, localBase, localIdx, hLt => by
    simp only [buildMerkleAuthPathKp]
    have hMul : localBase * (2 ^ (h + 1)) = (2 * localBase) * (2 ^ h) := by
      rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm (localBase * 2 ^ h) 2, Nat.mul_assoc]
    by_cases hHalf : localIdx < 2 ^ h
    · simp only [hHalf, ↓reduceIte, walkMerkleAuthPathKp]
      have hIdxEq : localBase * (2 ^ (h + 1)) + localIdx = (2 * localBase) * (2 ^ h) + localIdx := by rw [hMul]
      rw [hIdxEq, walkMerkleAuthPathKp_buildMerkleAuthPathKp suite pkSeed layer tree nodeKind keyPair leafFn h (2 * nodeIdx) (2 * localBase) localIdx hHalf]
      rfl
    · simp only [hHalf, ↓reduceIte, walkMerkleAuthPathKp]
      have hSubLt : localIdx - 2 ^ h < 2 ^ h := by rw [Nat.pow_succ] at hLt; omega
      have hIdxEq : localBase * (2 ^ (h + 1)) + localIdx = (2 * localBase + 1) * (2 ^ h) + (localIdx - 2 ^ h) := by
        rw [hMul, Nat.add_mul, Nat.one_mul, Nat.add_assoc, Nat.add_sub_of_le (Nat.le_of_not_lt hHalf)]
      rw [hIdxEq, walkMerkleAuthPathKp_buildMerkleAuthPathKp suite pkSeed layer tree nodeKind keyPair leafFn h (2 * nodeIdx + 1) (2 * localBase + 1) (localIdx - 2 ^ h) hSubLt]
      rfl

def walkMerkleAuthPathKp_collision_extract
    (suite : TweakableHashSuite) (pkSeed : List UInt8)
    (layer : UInt32) (tree : UInt64) (nodeKind : AdrsKind) (keyPair : UInt32) :
    ∀ (h nodeIdx localIdx : Nat) {leaf1 leaf2 : List UInt8} {path1 path2 : List (List UInt8)} {root : List UInt8},
      (leaf1 ≠ leaf2 ∨ path1 ≠ path2) →
      walkMerkleAuthPathKp suite pkSeed layer tree nodeKind keyPair h nodeIdx localIdx leaf1 path1 = some root →
      walkMerkleAuthPathKp suite pkSeed layer tree nodeKind keyPair h nodeIdx localIdx leaf2 path2 = some root →
      HashCollisionWitness suite.rawHash
  | 0, _, _, leaf1, leaf2, [], [], _, hDiff, h1, h2 => by
    simp only [walkMerkleAuthPathKp, Option.some.injEq] at h1 h2
    have hLeafEq : leaf1 = leaf2 := h1.trans h2.symm
    exact False.elim (by rcases hDiff with hne | hpne; exact hne hLeafEq; exact hpne rfl)
  | 0, _, _, _, _, [], _ :: _, _, _, _, h2 => by simp [walkMerkleAuthPathKp] at h2
  | 0, _, _, _, _, _ :: _, _, _, _, h1, _ => by simp [walkMerkleAuthPathKp] at h1
  | _ + 1, _, _, _, _, [], _, _, _, h1, _ => by simp [walkMerkleAuthPathKp] at h1
  | _ + 1, _, _, _, _, _ :: _, [], _, _, _, h2 => by simp [walkMerkleAuthPathKp] at h2
  | h + 1, nodeIdx, localIdx, leaf1, leaf2, sib1 :: rest1, sib2 :: rest2, root, hDiff, h1, h2 =>
    let adrs : HashAdrs := ⟨layer, tree, nodeKind, keyPair, UInt32.ofNat (h + 1), UInt32.ofNat nodeIdx⟩
    if hHalf : localIdx < 2 ^ h then
      match hSub1 : walkMerkleAuthPathKp suite pkSeed layer tree nodeKind keyPair h (2 * nodeIdx) localIdx leaf1 rest1,
            hSub2 : walkMerkleAuthPathKp suite pkSeed layer tree nodeKind keyPair h (2 * nodeIdx) localIdx leaf2 rest2 with
      | none, _ => False.elim (by
          unfold walkMerkleAuthPathKp at h1; simp only [hHalf, ↓reduceIte, hSub1] at h1; cases h1)
      | _, none => False.elim (by
          unfold walkMerkleAuthPathKp at h2; simp only [hHalf, ↓reduceIte, hSub2] at h2; cases h2)
      | some sub1, some sub2 =>
        have hRootEq : thNodeH suite pkSeed adrs sub1 sib1 = thNodeH suite pkSeed adrs sub2 sib2 := by
          unfold walkMerkleAuthPathKp at h1 h2
          simp only [hHalf, ↓reduceIte, hSub1, hSub2, Option.some.injEq] at h1 h2
          exact h1.trans h2.symm
        if hInputsNe : sub1 ≠ sub2 ∨ sib1 ≠ sib2 then
          match thCall_binds_or_collision suite hRootEq with
          | .inl ⟨_, _, _, hArgsEq⟩ =>
            False.elim (by
              simp only [List.cons.injEq, and_true] at hArgsEq
              rcases hInputsNe with hs | hsib; exact hs hArgsEq.1; exact hsib hArgsEq.2)
          | .inr col => col
        else
          have hSubEq : sub1 = sub2 := Decidable.of_not_not (fun hn => hInputsNe (.inl hn))
          have hSibEq : sib1 = sib2 := Decidable.of_not_not (fun hn => hInputsNe (.inr hn))
          have hRestDiff : leaf1 ≠ leaf2 ∨ rest1 ≠ rest2 := by
            if hL : leaf1 = leaf2 then
              right; intro hR; rcases hDiff with hLne | hPne; exact hLne hL; exact hPne (by rw [hSibEq, hR])
            else exact .inl hL
          walkMerkleAuthPathKp_collision_extract suite pkSeed layer tree nodeKind keyPair h (2 * nodeIdx) localIdx
            hRestDiff hSub1 (hSubEq ▸ hSub2)
    else
      match hSub1 : walkMerkleAuthPathKp suite pkSeed layer tree nodeKind keyPair h (2 * nodeIdx + 1) (localIdx - 2 ^ h) leaf1 rest1,
            hSub2 : walkMerkleAuthPathKp suite pkSeed layer tree nodeKind keyPair h (2 * nodeIdx + 1) (localIdx - 2 ^ h) leaf2 rest2 with
      | none, _ => False.elim (by
          unfold walkMerkleAuthPathKp at h1; simp only [hHalf, ↓reduceIte, hSub1] at h1; cases h1)
      | _, none => False.elim (by
          unfold walkMerkleAuthPathKp at h2; simp only [hHalf, ↓reduceIte, hSub2] at h2; cases h2)
      | some sub1, some sub2 =>
        have hRootEq : thNodeH suite pkSeed adrs sib1 sub1 = thNodeH suite pkSeed adrs sib2 sub2 := by
          unfold walkMerkleAuthPathKp at h1 h2
          simp only [hHalf, ↓reduceIte, hSub1, hSub2, Option.some.injEq] at h1 h2
          exact h1.trans h2.symm
        if hInputsNe : sib1 ≠ sib2 ∨ sub1 ≠ sub2 then
          match thCall_binds_or_collision suite hRootEq with
          | .inl ⟨_, _, _, hArgsEq⟩ =>
            False.elim (by
              simp only [List.cons.injEq, and_true] at hArgsEq
              rcases hInputsNe with hsib | hs; exact hsib hArgsEq.1; exact hs hArgsEq.2)
          | .inr col => col
        else
          have hSibEq : sib1 = sib2 := Decidable.of_not_not (fun hn => hInputsNe (.inl hn))
          have hSubEq : sub1 = sub2 := Decidable.of_not_not (fun hn => hInputsNe (.inr hn))
          have hRestDiff : leaf1 ≠ leaf2 ∨ rest1 ≠ rest2 := by
            if hL : leaf1 = leaf2 then
              right; intro hR; rcases hDiff with hLne | hPne; exact hLne hL; exact hPne (by rw [hSibEq, hR])
            else exact .inl hL
          walkMerkleAuthPathKp_collision_extract suite pkSeed layer tree nodeKind keyPair h (2 * nodeIdx + 1) (localIdx - 2 ^ h)
            hRestDiff hSub1 (hSubEq ▸ hSub2)

/-- Production `(j, u)` FORS leaf function at `(tree0, kp0)` for tree `j`. -/
def forsIndexedLeafFn (suite : TweakableHashSuite) (sk : PqSecretKey)
    (tree0 : UInt64) (kp0 j : Nat) : Nat → List UInt8 :=
  fun u => forsIndexedLeafHash suite sk.pkSeed tree0 kp0 j u
    (forsIndexedSecretLeaf suite sk tree0 kp0 j u)

theorem forsIndexedLeafFn_eq (suite : TweakableHashSuite) (sk : PqSecretKey)
    (tree0 : UInt64) (kp0 j u : Nat) :
    forsIndexedLeafFn suite sk tree0 kp0 j u =
      forsIndexedLeafHash suite sk.pkSeed tree0 kp0 j u
        (forsIndexedSecretLeaf suite sk tree0 kp0 j u) := by rfl

/-- Production FORS public key computation matching `tsw_baggy.rs:1691–1737`
    (explicit `key_pair = kp0` on `.forsTree` internal nodes and `(j, u)` leaf addressing). -/
def computeProductionForsPk (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (tree0 : UInt64) (kp0 : Nat) : List UInt8 :=
  let kpU32 := UInt32.ofNat kp0
  let roots := (List.range params.forsTrees).map fun j =>
    computeMerkleNodeKp suite sk.pkSeed 0 tree0 .forsTree kpU32
      (forsIndexedLeafFn suite sk tree0 kp0 j) params.forsHeight j 0
  thTweakTl suite sk.pkSeed ⟨0, tree0, .forsRoots, kpU32, 0, 0⟩ roots

theorem computeProductionForsPk_eq (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (tree0 : UInt64) (kp0 : Nat) :
    computeProductionForsPk suite params sk tree0 kp0 =
      let kpU32 := UInt32.ofNat kp0
      let roots := (List.range params.forsTrees).map fun j =>
        computeMerkleNodeKp suite sk.pkSeed 0 tree0 .forsTree kpU32
          (forsIndexedLeafFn suite sk tree0 kp0 j) params.forsHeight j 0
      thTweakTl suite sk.pkSeed ⟨0, tree0, .forsRoots, kpU32, 0, 0⟩ roots := by rfl

/-- Production FORS opening builder threading XOF-derived `idxs` directly (`tsw_baggy.rs:1691–1727`). -/
def buildProductionForsOpenings (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (tree0 : UInt64) (kp0 : Nat) (idxs : List Nat) : List ForsTreeOpening :=
  let kpU32 := UInt32.ofNat kp0
  (List.range params.forsTrees).map fun j =>
    let idxJ := idxs.getD j 0
    { secretVal := forsIndexedSecretLeaf suite sk tree0 kp0 j idxJ
      authPath  := buildMerkleAuthPathKp suite sk.pkSeed 0 tree0 .forsTree kpU32
                     (forsIndexedLeafFn suite sk tree0 kp0 j) params.forsHeight j 0 idxJ }

def recoverProductionForsTreeRoots (suite : TweakableHashSuite) (params : PqHashParams)
    (pkSeed : List UInt8) (treeIdx : UInt64) (kpIdx : Nat)
    (idxs : List Nat) (openings : List ForsTreeOpening) (j : Nat) : Nat → Option (List (List UInt8))
  | 0 => some []
  | rem + 1 =>
    let idxJ := idxs.getD j 0
    let op := openings.getD j ⟨[], []⟩
    let leafH := forsIndexedLeafHash suite pkSeed treeIdx kpIdx j idxJ op.secretVal
    match walkMerkleAuthPathKp suite pkSeed 0 treeIdx .forsTree (UInt32.ofNat kpIdx)
            params.forsHeight j idxJ leafH op.authPath with
    | none => none
    | some rJ =>
      match recoverProductionForsTreeRoots suite params pkSeed treeIdx kpIdx idxs openings (j + 1) rem with
      | none => none
      | some rs => some (rJ :: rs)

theorem recoverProductionForsTreeRoots_zero (suite : TweakableHashSuite) (params : PqHashParams)
    (pkSeed : List UInt8) (treeIdx : UInt64) (kpIdx : Nat)
    (idxs : List Nat) (openings : List ForsTreeOpening) (j : Nat) :
    recoverProductionForsTreeRoots suite params pkSeed treeIdx kpIdx idxs openings j 0 = some [] := by rfl

theorem recoverProductionForsTreeRoots_succ (suite : TweakableHashSuite) (params : PqHashParams)
    (pkSeed : List UInt8) (treeIdx : UInt64) (kpIdx : Nat)
    (idxs : List Nat) (openings : List ForsTreeOpening) (j rem : Nat) :
    recoverProductionForsTreeRoots suite params pkSeed treeIdx kpIdx idxs openings j (rem + 1) =
      let idxJ := idxs.getD j 0
      let op := openings.getD j ⟨[], []⟩
      let leafH := forsIndexedLeafHash suite pkSeed treeIdx kpIdx j idxJ op.secretVal
      match walkMerkleAuthPathKp suite pkSeed 0 treeIdx .forsTree (UInt32.ofNat kpIdx)
              params.forsHeight j idxJ leafH op.authPath with
      | none => none
      | some rJ =>
        match recoverProductionForsTreeRoots suite params pkSeed treeIdx kpIdx idxs openings (j + 1) rem with
        | none => none
        | some rs => some (rJ :: rs) := by rfl

/-- Production FORS public key recovery consuming XOF-derived `idxs` directly (`tsw_baggy.rs:1995–2036`). -/
def recoverProductionForsPk (suite : TweakableHashSuite) (params : PqHashParams)
    (pkSeed : List UInt8) (treeIdx : UInt64) (kpIdx : Nat)
    (idxs : List Nat) (openings : List ForsTreeOpening) : Option (List UInt8) :=
  if openings.length ≠ params.forsTrees || idxs.length ≠ params.forsTrees then none
  else
    match recoverProductionForsTreeRoots suite params pkSeed treeIdx kpIdx idxs openings 0 params.forsTrees with
    | none => none
    | some roots =>
      some (thTweakTl suite pkSeed ⟨0, treeIdx, .forsRoots, UInt32.ofNat kpIdx, 0, 0⟩ roots)

theorem recoverProductionForsPk_eq (suite : TweakableHashSuite) (params : PqHashParams)
    (pkSeed : List UInt8) (treeIdx : UInt64) (kpIdx : Nat)
    (idxs : List Nat) (openings : List ForsTreeOpening) :
    recoverProductionForsPk suite params pkSeed treeIdx kpIdx idxs openings =
      if openings.length ≠ params.forsTrees || idxs.length ≠ params.forsTrees then none
      else
        match recoverProductionForsTreeRoots suite params pkSeed treeIdx kpIdx idxs openings 0 params.forsTrees with
        | none => none
        | some roots =>
          some (thTweakTl suite pkSeed ⟨0, treeIdx, .forsRoots, UInt32.ofNat kpIdx, 0, 0⟩ roots) := by rfl

theorem recoverProductionForsPk_buildProductionForsOpenings
    (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (tree0 : UInt64) (kp0 : Nat) (idxs : List Nat)
    (hLen : idxs.length = params.forsTrees)
    (hBound : ∀ idx ∈ idxs, idx < 2 ^ params.forsHeight) :
    recoverProductionForsPk suite params sk.pkSeed tree0 kp0 idxs
      (buildProductionForsOpenings suite params sk tree0 kp0 idxs) =
    some (computeProductionForsPk suite params sk tree0 kp0) := by
  unfold recoverProductionForsPk buildProductionForsOpenings computeProductionForsPk
  let kpU32 := UInt32.ofNat kp0
  let ops := (List.range params.forsTrees).map fun j =>
    let idxJ := idxs.getD j 0
    { secretVal := forsIndexedSecretLeaf suite sk tree0 kp0 j idxJ
      authPath  := buildMerkleAuthPathKp suite sk.pkSeed 0 tree0 .forsTree kpU32
                     (forsIndexedLeafFn suite sk tree0 kp0 j) params.forsHeight j 0 idxJ : ForsTreeOpening }
  have hOpsLen : ops.length = params.forsTrees := by simp [ops]
  change (if ops.length ≠ params.forsTrees || idxs.length ≠ params.forsTrees then none else _) = _
  simp only [hOpsLen, hLen, ne_eq, not_true_eq_false, Bool.or_self]
  have hCollect : ∀ (rem j : Nat), j + rem = params.forsTrees →
      recoverProductionForsTreeRoots suite params sk.pkSeed tree0 kp0 idxs ops j rem =
      some ((List.range rem).map fun off =>
        computeMerkleNodeKp suite sk.pkSeed 0 tree0 .forsTree kpU32
          (forsIndexedLeafFn suite sk tree0 kp0 (j + off)) params.forsHeight (j + off) 0) := by
    intro rem
    induction rem with
    | zero => intro _ _; simp [recoverProductionForsTreeRoots]
    | succ rem ih =>
      intro j hjSum
      have hjLt : j < params.forsTrees := by omega
      simp only [recoverProductionForsTreeRoots]
      have hOpGet : ops.getD j (⟨[], []⟩ : ForsTreeOpening) =
          { secretVal := forsIndexedSecretLeaf suite sk tree0 kp0 j (idxs.getD j 0)
            authPath  := buildMerkleAuthPathKp suite sk.pkSeed 0 tree0 .forsTree kpU32
                           (forsIndexedLeafFn suite sk tree0 kp0 j) params.forsHeight j 0 (idxs.getD j 0) } :=
        list_getD_map_range params.forsTrees _ (⟨[], []⟩ : ForsTreeOpening) hjLt
      rw [hOpGet]
      dsimp only
      have hIdxLt : idxs.getD j 0 < 2 ^ params.forsHeight := by
        have hjIdxs : j < idxs.length := hLen ▸ hjLt
        rw [list_getD_eq_getElem idxs 0 hjIdxs]
        exact hBound _ (List.getElem_mem hjIdxs)
      have hWalk := walkMerkleAuthPathKp_buildMerkleAuthPathKp suite sk.pkSeed 0 tree0 .forsTree kpU32
        (forsIndexedLeafFn suite sk tree0 kp0 j) params.forsHeight j 0 (idxs.getD j 0) hIdxLt
      simp only [Nat.zero_mul, Nat.zero_add] at hWalk
      dsimp only [forsIndexedLeafFn] at hWalk
      change (match walkMerkleAuthPathKp suite sk.pkSeed 0 tree0 .forsTree kpU32 params.forsHeight j (idxs.getD j 0)
                (forsIndexedLeafHash suite sk.pkSeed tree0 kp0 j (idxs.getD j 0)
                  (forsIndexedSecretLeaf suite sk tree0 kp0 j (idxs.getD j 0)))
                (buildMerkleAuthPathKp suite sk.pkSeed 0 tree0 .forsTree kpU32
                  (forsIndexedLeafFn suite sk tree0 kp0 j) params.forsHeight j 0 (idxs.getD j 0)) with
              | none => none
              | some rJ => _) = _
      rw [hWalk, ih (j + 1) (by omega), list_range_succ_shift]
      simp only [Nat.add_zero, Option.some.injEq, List.cons.injEq, true_and]
      apply List.map_congr_left
      intro k _
      have hAssoc : j + 1 + k = j + (k + 1) := by omega
      rw [hAssoc]
  change (match recoverProductionForsTreeRoots suite params sk.pkSeed tree0 kp0 idxs ops 0 params.forsTrees with
          | none => none | some roots => _) = _
  rw [hCollect params.forsTrees 0 (by omega)]; simp; rfl

/-- Production stateless XOF derivation matching `derive_stateless_leaf_and_fors_indices`
    in `crates/qsag-core/src/tsw_baggy.rs:1590–1619`. -/
def deriveProductionStatelessInputs (suite : TweakableHashSuite) (params : PqHashParams)
    (rRand pkSeed pkRoot mu : List UInt8) : Option (Nat × List Nat) :=
  if !params.productionWellFormed || params.statefulJorts then none
  else
    let forsBytes := (params.forsTrees * params.forsHeight + 7) / 8
    let treeBits := params.numLayers * params.subtreeHeight
    let treeBytes := (treeBits + 7) / 8
    let digest := thXofMsg suite rRand pkSeed pkRoot mu (forsBytes + treeBytes)
    let forsSlice := digest.take forsBytes
    let treeSlice := digest.drop forsBytes
    some (extractBitWindow treeSlice 0 treeBits,
      (List.range params.forsTrees).map (fun j => extractBitWindow forsSlice (j * params.forsHeight) params.forsHeight))

theorem deriveProductionStatelessInputs_eq (suite : TweakableHashSuite) (params : PqHashParams)
    (rRand pkSeed pkRoot mu : List UInt8) :
    deriveProductionStatelessInputs suite params rRand pkSeed pkRoot mu =
      if !params.productionWellFormed || params.statefulJorts then none
      else
        let forsBytes := (params.forsTrees * params.forsHeight + 7) / 8
        let treeBits := params.numLayers * params.subtreeHeight
        let treeBytes := (treeBits + 7) / 8
        let digest := thXofMsg suite rRand pkSeed pkRoot mu (forsBytes + treeBytes)
        let forsSlice := digest.take forsBytes
        let treeSlice := digest.drop forsBytes
        some (extractBitWindow treeSlice 0 treeBits,
          (List.range params.forsTrees).map (fun j => extractBitWindow forsSlice (j * params.forsHeight) params.forsHeight)) := by rfl

theorem deriveProductionStatelessInputs_bounds (suite : TweakableHashSuite) (params : PqHashParams)
    (rRand pkSeed pkRoot mu : List UInt8) (leaf : Nat) (idxs : List Nat)
    (h : deriveProductionStatelessInputs suite params rRand pkSeed pkRoot mu = some (leaf, idxs)) :
    params.productionWellFormed = true ∧
    params.statefulJorts = false ∧
    leaf < 2 ^ (params.numLayers * params.subtreeHeight) ∧
    idxs.length = params.forsTrees ∧
    ∀ idx ∈ idxs, idx < 2 ^ params.forsHeight := by
  unfold deriveProductionStatelessInputs at h
  cases hWf : params.productionWellFormed
  · simp [hWf] at h
  · cases hSt : params.statefulJorts
    · simp only [hWf, hSt, Bool.not_true, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
        Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      refine ⟨rfl, rfl, Nat.mod_lt _ (Nat.two_pow_pos _), by simp, ?_⟩
      intro idx hMem
      simp only [List.mem_map] at hMem
      obtain ⟨_, _, rfl⟩ := hMem
      exact Nat.mod_lt _ (Nat.two_pow_pos _)
    · simp [hWf, hSt] at h

/-- Production hypertree layer digest selector matching `tsw_baggy.rs:1752–1780, 2046–2068`:
    uses `thHashLeafMsg` (`TAG_H_MSG`, 32 B) ONLY at stateful layer `0`, and `thHashInternalNode`
    (`TAG_H_INTERNAL`, 32 B, zero `rRand`) at ALL upper layers (`layerIdx ≥ 1`) AND stateless layer `0`. -/
def productionLayerDigest (suite : TweakableHashSuite) (params : PqHashParams)
    (rRand pkSeed pkRoot curRoot : List UInt8)
    (layerIdx : Nat) (treeIdx : UInt64) (kpIdx : UInt32) (ctr : Nat) : List UInt8 :=
  if params.statefulJorts && decide (layerIdx = 0) then
    thHashLeafMsg suite rRand pkSeed pkRoot curRoot treeIdx kpIdx ctr
  else
    thHashInternalNode suite pkSeed pkRoot curRoot (UInt32.ofNat layerIdx) treeIdx kpIdx ctr

theorem productionLayerDigest_eq (suite : TweakableHashSuite) (params : PqHashParams)
    (rRand pkSeed pkRoot curRoot : List UInt8)
    (layerIdx : Nat) (treeIdx : UInt64) (kpIdx : UInt32) (ctr : Nat) :
    productionLayerDigest suite params rRand pkSeed pkRoot curRoot layerIdx treeIdx kpIdx ctr =
      if params.statefulJorts && decide (layerIdx = 0) then
        thHashLeafMsg suite rRand pkSeed pkRoot curRoot treeIdx kpIdx ctr
      else
        thHashInternalNode suite pkSeed pkRoot curRoot (UInt32.ofNat layerIdx) treeIdx kpIdx ctr := by rfl

theorem productionLayerDigest_length (suite : TweakableHashSuite) (params : PqHashParams)
    (rRand pkSeed pkRoot curRoot : List UInt8)
    (layerIdx : Nat) (treeIdx : UInt64) (kpIdx : UInt32) (ctr : Nat) :
    (productionLayerDigest suite params rRand pkSeed pkRoot curRoot layerIdx treeIdx kpIdx ctr).length = 32 := by
  unfold productionLayerDigest
  split
  · exact thHashLeafMsg_length _ _ _ _ _ _ _ _
  · exact thHashInternalNode_length _ _ _ _ _ _ _ _

/-- Production hypertree layer verifier matching `tsw_baggy.rs:2039–2107`. -/
def verifyProductionHypertreeLayers (suite : TweakableHashSuite) (params : PqHashParams)
    (pkSeed pkRoot rRand : List UInt8) :
    Nat → Nat → List UInt8 → List LayerXmssSig → Option (List UInt8)
  | _, _, curRoot, [] => some curRoot
  | layerIdx, globalIdx, curRoot, lsig :: rest =>
    if !(decide (lsig.tswCtr < 2 ^ 32)) then none
    else
      let subLeaves := 2 ^ params.subtreeHeight
      let kpIdx := globalIdx % subLeaves
      let kpU32 := UInt32.ofNat kpIdx
      let treeIdxNat := globalIdx / subLeaves
      let treeIdx := UInt64.ofNat treeIdxNat
      let layerU32 := UInt32.ofNat layerIdx
      let hmsg := productionLayerDigest suite params rRand pkSeed pkRoot curRoot layerIdx treeIdx kpU32 lsig.tswCtr
      match extractBaseWDigitsChecked params.w params.ell1 hmsg with
      | none => none
      | some digits =>
        if !(checkTargetSum params.w params.ell1 params.targetSum digits) then none
        else if lsig.wotsChains.length ≠ params.ell1 then none
        else
          let wotsPk := recoverWotsPkFromSig suite params pkSeed layerU32 treeIdx kpIdx digits lsig.wotsChains
          match walkMerkleAuthPathKp suite pkSeed layerU32 treeIdx .tree 0 params.subtreeHeight 0 kpIdx wotsPk lsig.authPath with
          | none => none
          | some nextSubtreeRoot =>
            verifyProductionHypertreeLayers suite params pkSeed pkRoot rRand (layerIdx + 1) treeIdxNat nextSubtreeRoot rest

theorem verifyProductionHypertreeLayers_nil (suite : TweakableHashSuite) (params : PqHashParams)
    (pkSeed pkRoot rRand : List UInt8) (layerIdx globalIdx : Nat) (curRoot : List UInt8) :
    verifyProductionHypertreeLayers suite params pkSeed pkRoot rRand layerIdx globalIdx curRoot [] = some curRoot := by rfl

theorem verifyProductionHypertreeLayers_cons (suite : TweakableHashSuite) (params : PqHashParams)
    (pkSeed pkRoot rRand : List UInt8) (layerIdx globalIdx : Nat) (curRoot : List UInt8)
    (lsig : LayerXmssSig) (rest : List LayerXmssSig) :
    verifyProductionHypertreeLayers suite params pkSeed pkRoot rRand layerIdx globalIdx curRoot (lsig :: rest) =
      if !(decide (lsig.tswCtr < 2 ^ 32)) then none
      else
        let subLeaves := 2 ^ params.subtreeHeight
        let kpIdx := globalIdx % subLeaves
        let kpU32 := UInt32.ofNat kpIdx
        let treeIdxNat := globalIdx / subLeaves
        let treeIdx := UInt64.ofNat treeIdxNat
        let layerU32 := UInt32.ofNat layerIdx
        let hmsg := productionLayerDigest suite params rRand pkSeed pkRoot curRoot layerIdx treeIdx kpU32 lsig.tswCtr
        match extractBaseWDigitsChecked params.w params.ell1 hmsg with
        | none => none
        | some digits =>
          if !(checkTargetSum params.w params.ell1 params.targetSum digits) then none
          else if lsig.wotsChains.length ≠ params.ell1 then none
          else
            let wotsPk := recoverWotsPkFromSig suite params pkSeed layerU32 treeIdx kpIdx digits lsig.wotsChains
            match walkMerkleAuthPathKp suite pkSeed layerU32 treeIdx .tree 0 params.subtreeHeight 0 kpIdx wotsPk lsig.authPath with
            | none => none
            | some nextSubtreeRoot =>
              verifyProductionHypertreeLayers suite params pkSeed pkRoot rRand (layerIdx + 1) treeIdxNat nextSubtreeRoot rest := by rfl

/-- Production hypertree layer signer matching `tsw_baggy.rs:1740–1824`. -/
def signProductionHypertreeLayers (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (pkRoot rRand : List UInt8) (maxGrind : Nat) :
    Nat → Nat → List UInt8 → Nat → Option (List LayerXmssSig)
  | _, _, _, 0 => some []
  | layerIdx, globalIdx, curRoot, rem + 1 =>
    let subLeaves := 2 ^ params.subtreeHeight
    let kpIdx := globalIdx % subLeaves
    let kpU32 := UInt32.ofNat kpIdx
    let treeIdxNat := globalIdx / subLeaves
    let treeIdx := UInt64.ofNat treeIdxNat
    let layerU32 := UInt32.ofNat layerIdx
    let grindRes :=
      if params.statefulJorts && decide (layerIdx = 0) then
        grindTswLeafCounterAux suite params.w params.ell1 params.targetSum
          rRand sk.pkSeed pkRoot curRoot treeIdx kpU32 0 maxGrind
      else
        grindTswInternalCounterAux suite params.w params.ell1 params.targetSum
          sk.pkSeed pkRoot curRoot layerU32 treeIdx kpU32 0 maxGrind
    match grindRes with
    | none => none
    | some (ctr, digits, _) =>
      let wotsChains := (List.range params.ell1).map fun r =>
        let dr := digits.getD r 0
        wotsChainSteps suite sk.pkSeed layerU32 treeIdx kpIdx r 0 dr
          (wotsSecretBase suite sk layerU32 treeIdx kpIdx r)
      let authPath := buildMerkleAuthPathKp suite sk.pkSeed layerU32 treeIdx .tree 0
        (computeWotsPk suite params sk layerU32 treeIdx) params.subtreeHeight 0 0 kpIdx
      let nextRoot := computeXmssSubtreeRoot suite params sk layerU32 treeIdx
      match signProductionHypertreeLayers suite params sk pkRoot rRand maxGrind (layerIdx + 1) treeIdxNat nextRoot rem with
      | none => none
      | some restSigs =>
        some ({ tswCtr := ctr, wotsChains := wotsChains, authPath := authPath } :: restSigs)

theorem signProductionHypertreeLayers_zero (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (pkRoot rRand : List UInt8) (maxGrind layerIdx globalIdx : Nat) (curRoot : List UInt8) :
    signProductionHypertreeLayers suite params sk pkRoot rRand maxGrind layerIdx globalIdx curRoot 0 = some [] := by rfl

theorem signProductionHypertreeLayers_succ (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (pkRoot rRand : List UInt8) (maxGrind layerIdx globalIdx : Nat) (curRoot : List UInt8) (rem : Nat) :
    signProductionHypertreeLayers suite params sk pkRoot rRand maxGrind layerIdx globalIdx curRoot (rem + 1) =
      let subLeaves := 2 ^ params.subtreeHeight
      let kpIdx := globalIdx % subLeaves
      let kpU32 := UInt32.ofNat kpIdx
      let treeIdxNat := globalIdx / subLeaves
      let treeIdx := UInt64.ofNat treeIdxNat
      let layerU32 := UInt32.ofNat layerIdx
      let grindRes :=
        if params.statefulJorts && decide (layerIdx = 0) then
          grindTswLeafCounterAux suite params.w params.ell1 params.targetSum
            rRand sk.pkSeed pkRoot curRoot treeIdx kpU32 0 maxGrind
        else
          grindTswInternalCounterAux suite params.w params.ell1 params.targetSum
            sk.pkSeed pkRoot curRoot layerU32 treeIdx kpU32 0 maxGrind
      match grindRes with
      | none => none
      | some (ctr, digits, _) =>
        let wotsChains := (List.range params.ell1).map fun r =>
          let dr := digits.getD r 0
          wotsChainSteps suite sk.pkSeed layerU32 treeIdx kpIdx r 0 dr
            (wotsSecretBase suite sk layerU32 treeIdx kpIdx r)
        let authPath := buildMerkleAuthPathKp suite sk.pkSeed layerU32 treeIdx .tree 0
          (computeWotsPk suite params sk layerU32 treeIdx) params.subtreeHeight 0 0 kpIdx
        let nextRoot := computeXmssSubtreeRoot suite params sk layerU32 treeIdx
        match signProductionHypertreeLayers suite params sk pkRoot rRand maxGrind (layerIdx + 1) treeIdxNat nextRoot rem with
        | none => none
        | some restSigs =>
          some ({ tswCtr := ctr, wotsChains := wotsChains, authPath := authPath } :: restSigs) := by rfl

private theorem grindRes_production_sound (suite : TweakableHashSuite) (params : PqHashParams)
    (rRand pkSeed pkRoot curRoot : List UInt8) (layerIdx : Nat) (treeIdx : UInt64) (kpU32 : UInt32)
    (maxGrind ctr : Nat) (digits : List Nat) (hmsg : List UInt8)
    (h : (if params.statefulJorts && decide (layerIdx = 0) then
            grindTswLeafCounterAux suite params.w params.ell1 params.targetSum rRand pkSeed pkRoot curRoot treeIdx kpU32 0 maxGrind
          else
            grindTswInternalCounterAux suite params.w params.ell1 params.targetSum pkSeed pkRoot curRoot (UInt32.ofNat layerIdx) treeIdx kpU32 0 maxGrind) =
         some (ctr, digits, hmsg)) :
    ctr < 2 ^ 32 ∧
    hmsg = productionLayerDigest suite params rRand pkSeed pkRoot curRoot layerIdx treeIdx kpU32 ctr ∧
    extractBaseWDigitsChecked params.w params.ell1 hmsg = some digits ∧
    checkTargetSum params.w params.ell1 params.targetSum digits = true := by
  unfold productionLayerDigest
  split at h
  · rename_i hCond
    simp only [hCond, ↓reduceIte]
    exact grindTswLeafCounterAux_sound h
  · rename_i hCond
    simp only [hCond]
    exact grindTswInternalCounterAux_sound h

theorem signProductionHypertreeLayers_sound
    (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (pkRoot rRand : List UInt8) (maxGrind : Nat) :
    ∀ (rem layerIdx globalIdx : Nat) (curRoot : List UInt8) (layerSigs : List LayerXmssSig),
      0 < rem →
      globalIdx < 2 ^ (rem * params.subtreeHeight) →
      signProductionHypertreeLayers suite params sk pkRoot rRand maxGrind layerIdx globalIdx curRoot rem = some layerSigs →
      layerSigs.length = rem ∧
      verifyProductionHypertreeLayers suite params sk.pkSeed pkRoot rRand layerIdx globalIdx curRoot layerSigs =
        some (computeXmssSubtreeRoot suite params sk (UInt32.ofNat (layerIdx + rem - 1)) 0)
  | 0, _, _, _, _, hPos, _, _ => by omega
  | 1, layerIdx, globalIdx, curRoot, layerSigs, _, hIdxLt, hSign => by
    rw [signProductionHypertreeLayers_succ] at hSign
    dsimp only at hSign
    cases hGrind : (if params.statefulJorts && decide (layerIdx = 0) then
        grindTswLeafCounterAux suite params.w params.ell1 params.targetSum rRand sk.pkSeed pkRoot curRoot
          (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight)) (UInt32.ofNat (globalIdx % 2 ^ params.subtreeHeight)) 0 maxGrind
      else
        grindTswInternalCounterAux suite params.w params.ell1 params.targetSum sk.pkSeed pkRoot curRoot
          (UInt32.ofNat layerIdx) (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight))
          (UInt32.ofNat (globalIdx % 2 ^ params.subtreeHeight)) 0 maxGrind) with
    | none => rw [hGrind] at hSign; cases hSign
    | some triple =>
      rcases triple with ⟨ctr, digits, hmsgG⟩
      rw [hGrind] at hSign
      simp only [signProductionHypertreeLayers_zero, Option.some.injEq] at hSign
      subst hSign
      obtain ⟨hCtrLt, hMsgEq, hExt, hChk⟩ := grindRes_production_sound suite params rRand sk.pkSeed pkRoot curRoot
        layerIdx (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight))
        (UInt32.ofNat (globalIdx % 2 ^ params.subtreeHeight)) maxGrind ctr digits hmsgG hGrind
      have hSubPos : 0 < 2 ^ params.subtreeHeight := Nat.two_pow_pos _
      have hGlobalBound : globalIdx < 2 ^ params.subtreeHeight := by simpa [Nat.one_mul] using hIdxLt
      have hDiv0 : globalIdx / 2 ^ params.subtreeHeight = 0 := Nat.div_eq_of_lt hGlobalBound
      refine ⟨rfl, ?_⟩
      rw [verifyProductionHypertreeLayers_cons]
      simp only [hCtrLt, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rw [← hMsgEq, hExt]
      dsimp only
      have hChainsLen : ((List.range params.ell1).map fun r =>
          wotsChainSteps suite sk.pkSeed (UInt32.ofNat layerIdx)
            (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight))
            (globalIdx % 2 ^ params.subtreeHeight) r 0 (digits.getD r 0)
            (wotsSecretBase suite sk (UInt32.ofNat layerIdx)
              (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight))
              (globalIdx % 2 ^ params.subtreeHeight) r)).length = params.ell1 := by simp
      simp only [hChk, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hChainsLen, ne_eq, not_true_eq_false]
      have hWotsEq := recoverWotsPkFromSig_eq_computeWotsPk suite params sk
        (UInt32.ofNat layerIdx) (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight))
        (globalIdx % 2 ^ params.subtreeHeight) digits hChk
      dsimp only at hWotsEq
      rw [hWotsEq]
      have hWalk := walkMerkleAuthPathKp_buildMerkleAuthPathKp suite sk.pkSeed
        (UInt32.ofNat layerIdx) (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight)) .tree 0
        (computeWotsPk suite params sk (UInt32.ofNat layerIdx) (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight)))
        params.subtreeHeight 0 0 (globalIdx % 2 ^ params.subtreeHeight) (Nat.mod_lt _ hSubPos)
      simp only [Nat.zero_mul, Nat.zero_add] at hWalk
      rw [hWalk, computeMerkleNodeKp_zero_eq]
      dsimp only
      rw [verifyProductionHypertreeLayers_nil, computeXmssSubtreeRoot_eq, hDiv0, Nat.add_sub_cancel]
      rfl
  | rem + 2, layerIdx, globalIdx, curRoot, layerSigs, _, hIdxLt, hSign => by
    rw [signProductionHypertreeLayers_succ] at hSign
    dsimp only at hSign
    cases hGrind : (if params.statefulJorts && decide (layerIdx = 0) then
        grindTswLeafCounterAux suite params.w params.ell1 params.targetSum rRand sk.pkSeed pkRoot curRoot
          (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight)) (UInt32.ofNat (globalIdx % 2 ^ params.subtreeHeight)) 0 maxGrind
      else
        grindTswInternalCounterAux suite params.w params.ell1 params.targetSum sk.pkSeed pkRoot curRoot
          (UInt32.ofNat layerIdx) (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight))
          (UInt32.ofNat (globalIdx % 2 ^ params.subtreeHeight)) 0 maxGrind) with
    | none => rw [hGrind] at hSign; cases hSign
    | some triple =>
      rcases triple with ⟨ctr, digits, hmsgG⟩
      rw [hGrind] at hSign
      dsimp only at hSign
      cases hRest : signProductionHypertreeLayers suite params sk pkRoot rRand maxGrind
          (layerIdx + 1) (globalIdx / 2 ^ params.subtreeHeight)
          (computeXmssSubtreeRoot suite params sk (UInt32.ofNat layerIdx)
            (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight))) (rem + 1) with
      | none => rw [hRest] at hSign; cases hSign
      | some restSigs =>
        rw [hRest] at hSign
        simp only [Option.some.injEq] at hSign
        subst hSign
        obtain ⟨hCtrLt, hMsgEq, hExt, hChk⟩ := grindRes_production_sound suite params rRand sk.pkSeed pkRoot curRoot
          layerIdx (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight))
          (UInt32.ofNat (globalIdx % 2 ^ params.subtreeHeight)) maxGrind ctr digits hmsgG hGrind
        have hSubPos : 0 < 2 ^ params.subtreeHeight := Nat.two_pow_pos _
        have hTreeLt : globalIdx / 2 ^ params.subtreeHeight < 2 ^ ((rem + 1) * params.subtreeHeight) := by
          have hPow : 2 ^ ((rem + 2) * params.subtreeHeight) =
              2 ^ ((rem + 1) * params.subtreeHeight) * 2 ^ params.subtreeHeight := by
            rw [Nat.succ_mul, Nat.pow_add]
          exact (Nat.div_lt_iff_lt_mul hSubPos).mpr (hPow ▸ hIdxLt)
        obtain ⟨hRestLen, hRestVer⟩ := signProductionHypertreeLayers_sound suite params sk pkRoot rRand maxGrind
          (rem + 1) (layerIdx + 1) (globalIdx / 2 ^ params.subtreeHeight)
          (computeXmssSubtreeRoot suite params sk (UInt32.ofNat layerIdx)
            (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight)))
          restSigs (by omega) hTreeLt hRest
        refine ⟨by simp [hRestLen], ?_⟩
        rw [verifyProductionHypertreeLayers_cons]
        simp only [hCtrLt, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        rw [← hMsgEq, hExt]
        dsimp only
        have hChainsLen : ((List.range params.ell1).map fun r =>
            wotsChainSteps suite sk.pkSeed (UInt32.ofNat layerIdx)
              (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight))
              (globalIdx % 2 ^ params.subtreeHeight) r 0 (digits.getD r 0)
              (wotsSecretBase suite sk (UInt32.ofNat layerIdx)
                (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight))
                (globalIdx % 2 ^ params.subtreeHeight) r)).length = params.ell1 := by simp
        simp only [hChk, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hChainsLen, ne_eq, not_true_eq_false]
        have hWotsEq := recoverWotsPkFromSig_eq_computeWotsPk suite params sk
          (UInt32.ofNat layerIdx) (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight))
          (globalIdx % 2 ^ params.subtreeHeight) digits hChk
        dsimp only at hWotsEq
        rw [hWotsEq]
        have hWalk := walkMerkleAuthPathKp_buildMerkleAuthPathKp suite sk.pkSeed
          (UInt32.ofNat layerIdx) (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight)) .tree 0
          (computeWotsPk suite params sk (UInt32.ofNat layerIdx)
            (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight)))
          params.subtreeHeight 0 0 (globalIdx % 2 ^ params.subtreeHeight) (Nat.mod_lt _ hSubPos)
        simp only [Nat.zero_mul, Nat.zero_add] at hWalk
        rw [hWalk, computeMerkleNodeKp_zero_eq, ← computeXmssSubtreeRoot_eq]
        dsimp only
        rw [hRestVer]
        have hTopLayerEq : layerIdx + 1 + (rem + 1) - 1 = layerIdx + (rem + 2) - 1 := by omega
        rw [hTopLayerEq]

/-- Production unified verifier matching `verify_pq_hash_sig` in `crates/qsag-core/src/tsw_baggy.rs:1955–2120`
    byte-for-byte. -/
def verifyProductionPqHashSig (suite : TweakableHashSuite) (params : PqHashParams)
    (pk : PqPublicKey) (msg : List UInt8) (sig : PqHashSig) : Bool :=
  if !params.productionWellFormed || !params.productionLeafIdxInRange sig.leafGlobalIdx then false
  else if sig.layerSigs.length ≠ params.numLayers || sig.msgTswCtr ≠ 0 then false
  else
    let mu := thPreHash suite pk.pkSeed pk.pkRoot msg
    if params.statefulJorts then
      if !sig.forsOpenings.isEmpty then false
      else
        match verifyProductionHypertreeLayers suite params pk.pkSeed pk.pkRoot sig.rRand 0 sig.leafGlobalIdx mu sig.layerSigs with
        | some computedTopRoot => decide (computedTopRoot = pk.pkRoot)
        | none => false
    else
      if sig.forsOpenings.length ≠ params.forsTrees then false
      else
        match deriveProductionStatelessInputs suite params sig.rRand pk.pkSeed pk.pkRoot mu with
        | none => false
        | some (derivedLeafIdx, idxs) =>
          if sig.leafGlobalIdx ≠ derivedLeafIdx then false
          else
            let subLeaves := 2 ^ params.subtreeHeight
            let kp0 := sig.leafGlobalIdx % subLeaves
            let tree0 := UInt64.ofNat (sig.leafGlobalIdx / subLeaves)
            match recoverProductionForsPk suite params pk.pkSeed tree0 kp0 idxs sig.forsOpenings with
            | none => false
            | some forsPk =>
              match verifyProductionHypertreeLayers suite params pk.pkSeed pk.pkRoot sig.rRand 0 sig.leafGlobalIdx forsPk sig.layerSigs with
              | some computedTopRoot => decide (computedTopRoot = pk.pkRoot)
              | none => false

theorem verifyProductionPqHashSig_eq (suite : TweakableHashSuite) (params : PqHashParams)
    (pk : PqPublicKey) (msg : List UInt8) (sig : PqHashSig) :
    verifyProductionPqHashSig suite params pk msg sig =
      if !params.productionWellFormed || !params.productionLeafIdxInRange sig.leafGlobalIdx then false
      else if sig.layerSigs.length ≠ params.numLayers || sig.msgTswCtr ≠ 0 then false
      else
        let mu := thPreHash suite pk.pkSeed pk.pkRoot msg
        if params.statefulJorts then
          if !sig.forsOpenings.isEmpty then false
          else
            match verifyProductionHypertreeLayers suite params pk.pkSeed pk.pkRoot sig.rRand 0 sig.leafGlobalIdx mu sig.layerSigs with
            | some computedTopRoot => decide (computedTopRoot = pk.pkRoot)
            | none => false
        else
          if sig.forsOpenings.length ≠ params.forsTrees then false
          else
            match deriveProductionStatelessInputs suite params sig.rRand pk.pkSeed pk.pkRoot mu with
            | none => false
            | some (derivedLeafIdx, idxs) =>
              if sig.leafGlobalIdx ≠ derivedLeafIdx then false
              else
                let subLeaves := 2 ^ params.subtreeHeight
                let kp0 := sig.leafGlobalIdx % subLeaves
                let tree0 := UInt64.ofNat (sig.leafGlobalIdx / subLeaves)
                match recoverProductionForsPk suite params pk.pkSeed tree0 kp0 idxs sig.forsOpenings with
                | none => false
                | some forsPk =>
                  match verifyProductionHypertreeLayers suite params pk.pkSeed pk.pkRoot sig.rRand 0 sig.leafGlobalIdx forsPk sig.layerSigs with
                  | some computedTopRoot => decide (computedTopRoot = pk.pkRoot)
                  | none => false := by rfl

/-- Production core hypertree + FORS signer matching `sign_hypertree_core` (`tsw_baggy.rs:1670–1837`),
    including mandatory self-verification (`verifyProductionPqHashSig`) before returning `some sig`. -/
def signProductionHypertreeCore (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (pk : PqPublicKey) (msg mu rRand : List UInt8)
    (leafGlobalIdx : Nat) (forsIdxs : Option (List Nat)) (maxGrind : Nat) : Option PqHashSig :=
  let subLeaves := 2 ^ params.subtreeHeight
  match (if params.statefulJorts then some ([], mu)
         else
           match forsIdxs with
           | none => none
           | some idxs =>
             let kp0 := leafGlobalIdx % subLeaves
             let tree0 := UInt64.ofNat (leafGlobalIdx / subLeaves)
             some (buildProductionForsOpenings suite params sk tree0 kp0 idxs,
                   computeProductionForsPk suite params sk tree0 kp0)) with
  | none => none
  | some (forsOpenings, curRoot) =>
    match signProductionHypertreeLayers suite params sk pk.pkRoot rRand maxGrind 0 leafGlobalIdx curRoot params.numLayers with
    | none => none
    | some layerSigs =>
      let sig : PqHashSig :=
        { rRand := rRand
          msgTswCtr := 0
          leafGlobalIdx := leafGlobalIdx
          forsOpenings := forsOpenings
          layerSigs := layerSigs }
      if verifyProductionPqHashSig suite params pk msg sig then some sig else none

/-- Production stateless signer matching `eval_single_sign_stateless` (`tsw_baggy.rs:1843–1874`):
    derives `(leafGlobalIdx, forsIdxs)` from `deriveProductionStatelessInputs` (`thXofMsg`),
    threads `forsIdxs` into `(j, u)`-addressed FORS with `kp0` Merkle binding, signs `forsPk`
    and all upper XMSS layers via `thHashInternalNode` (`H_INTERNAL`), sets `msgTswCtr = 0`,
    and self-verifies before release. -/
def evalProductionStatelessSign (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (msg optRand : List UInt8) (maxGrind : Nat) : Option PqHashSig :=
  if params.statefulJorts || !params.productionWellFormed then none
  else
    let pk := derivePublicKey suite params sk
    let mu := thPreHash suite pk.pkSeed pk.pkRoot msg
    let rRand := thPrfMsg suite sk.skPrf optRand mu
    match deriveProductionStatelessInputs suite params rRand pk.pkSeed pk.pkRoot mu with
    | none => none
    | some (leafGlobalIdx, forsIdxs) =>
      signProductionHypertreeCore suite params sk pk msg mu rRand leafGlobalIdx (some forsIdxs) maxGrind

theorem evalProductionStatelessSign_eq (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (msg optRand : List UInt8) (maxGrind : Nat) :
    evalProductionStatelessSign suite params sk msg optRand maxGrind =
      if params.statefulJorts || !params.productionWellFormed then none
      else
        let pk := derivePublicKey suite params sk
        let mu := thPreHash suite pk.pkSeed pk.pkRoot msg
        let rRand := thPrfMsg suite sk.skPrf optRand mu
        match deriveProductionStatelessInputs suite params rRand pk.pkSeed pk.pkRoot mu with
        | none => none
        | some (leafGlobalIdx, forsIdxs) =>
          signProductionHypertreeCore suite params sk pk msg mu rRand leafGlobalIdx (some forsIdxs) maxGrind := by rfl

/-- Production stateful signer matching `sign_stateful_with_latch` (`tsw_baggy.rs:1879–1913`):
    enforces `params.statefulJorts && params.productionWellFormed && params.productionLeafIdxInRange epoch`,
    signs layer `0` with `thHashLeafMsg` (`TAG_H_MSG`, 32 B) and upper layers `1 .. d-1` with
    `thHashInternalNode` (`TAG_H_INTERNAL`, 32 B), and self-verifies before release. -/
def evalProductionStatefulSign (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (msg optRand : List UInt8) (epoch maxGrind : Nat) : Option PqHashSig :=
  if !params.statefulJorts || !params.productionWellFormed || !params.productionLeafIdxInRange epoch then none
  else
    let pk := derivePublicKey suite params sk
    let mu := thPreHash suite pk.pkSeed pk.pkRoot msg
    let rRand := thPrfMsg suite sk.skPrf optRand mu
    signProductionHypertreeCore suite params sk pk msg mu rRand epoch none maxGrind

theorem evalProductionStatefulSign_eq (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (msg optRand : List UInt8) (epoch maxGrind : Nat) :
    evalProductionStatefulSign suite params sk msg optRand epoch maxGrind =
      if !params.statefulJorts || !params.productionWellFormed || !params.productionLeafIdxInRange epoch then none
      else
        let pk := derivePublicKey suite params sk
        let mu := thPreHash suite pk.pkSeed pk.pkRoot msg
        let rRand := thPrfMsg suite sk.skPrf optRand mu
        signProductionHypertreeCore suite params sk pk msg mu rRand epoch none maxGrind := by rfl

private theorem signProductionHypertreeCore_verifies
    (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (pk : PqPublicKey) (msg mu rRand : List UInt8)
    (leafGlobalIdx : Nat) (forsIdxs : Option (List Nat)) (maxGrind : Nat) (sig : PqHashSig)
    (h : signProductionHypertreeCore suite params sk pk msg mu rRand leafGlobalIdx forsIdxs maxGrind = some sig) :
    verifyProductionPqHashSig suite params pk msg sig = true := by
  unfold signProductionHypertreeCore at h
  dsimp only at h
  cases hInit : (if params.statefulJorts then some ([], mu)
      else match forsIdxs with
      | none => none
      | some idxs =>
        let kp0 := leafGlobalIdx % (2 ^ params.subtreeHeight)
        let tree0 := UInt64.ofNat (leafGlobalIdx / (2 ^ params.subtreeHeight))
        some (buildProductionForsOpenings suite params sk tree0 kp0 idxs,
              computeProductionForsPk suite params sk tree0 kp0)) with
  | none => rw [hInit] at h; cases h
  | some pair =>
    rcases pair with ⟨forsOpenings, curRoot⟩
    rw [hInit] at h
    dsimp only at h
    cases hLayers : signProductionHypertreeLayers suite params sk pk.pkRoot rRand maxGrind 0 leafGlobalIdx curRoot params.numLayers with
    | none => rw [hLayers] at h; cases h
    | some layerSigs =>
      rw [hLayers] at h
      dsimp only at h
      cases hVer : verifyProductionPqHashSig suite params pk msg
          { rRand := rRand, msgTswCtr := 0, leafGlobalIdx := leafGlobalIdx,
            forsOpenings := forsOpenings, layerSigs := layerSigs } with
      | false => rw [hVer] at h; simp at h
      | true =>
        rw [hVer] at h
        simp only [↓reduceIte, Option.some.injEq] at h
        subst h
        exact hVer

theorem verifyProductionPqHashSig_evalProductionStatelessSign
    (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (msg optRand : List UInt8) (maxGrind : Nat) (sig : PqHashSig)
    (hSign : evalProductionStatelessSign suite params sk msg optRand maxGrind = some sig) :
    verifyProductionPqHashSig suite params (derivePublicKey suite params sk) msg sig = true := by
  rw [evalProductionStatelessSign_eq] at hSign
  by_cases hBad : (params.statefulJorts || !params.productionWellFormed) = true
  · simp [hBad] at hSign
  · simp only [hBad, Bool.false_eq_true, ↓reduceIte] at hSign
    cases hD : deriveProductionStatelessInputs suite params
        (thPrfMsg suite sk.skPrf optRand
          (thPreHash suite (derivePublicKey suite params sk).pkSeed (derivePublicKey suite params sk).pkRoot msg))
        (derivePublicKey suite params sk).pkSeed (derivePublicKey suite params sk).pkRoot
        (thPreHash suite (derivePublicKey suite params sk).pkSeed (derivePublicKey suite params sk).pkRoot msg) with
    | none => rw [hD] at hSign; cases hSign
    | some pr =>
      rcases pr with ⟨leafGlobalIdx, forsIdxs⟩
      rw [hD] at hSign
      exact signProductionHypertreeCore_verifies _ _ _ _ _ _ _ _ _ _ _ hSign

theorem verifyProductionPqHashSig_evalProductionStatefulSign
    (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (msg optRand : List UInt8) (epoch maxGrind : Nat) (sig : PqHashSig)
    (hSign : evalProductionStatefulSign suite params sk msg optRand epoch maxGrind = some sig) :
    verifyProductionPqHashSig suite params (derivePublicKey suite params sk) msg sig = true := by
  rw [evalProductionStatefulSign_eq] at hSign
  by_cases hBad : (!params.statefulJorts || !params.productionWellFormed || !params.productionLeafIdxInRange epoch) = true
  · simp [hBad] at hSign
  · simp only [hBad, Bool.false_eq_true, ↓reduceIte] at hSign
    exact signProductionHypertreeCore_verifies _ _ _ _ _ _ _ _ _ _ _ hSign

/-- Non-vacuity / constructive completeness of the production verifier on honest layer signatures
    (proves `signProductionHypertreeCore`'s self-check always succeeds whenever `signProductionHypertreeLayers`
    succeeds on valid parameters and XOF/epoch inputs!). -/
theorem signProductionHypertreeCore_stateless_complete
    (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (msg optRand : List UInt8) (maxGrind leaf : Nat)
    (idxs : List Nat) (layerSigs : List LayerXmssSig)
    (hD : deriveProductionStatelessInputs suite params
            (thPrfMsg suite sk.skPrf optRand
              (thPreHash suite sk.pkSeed (derivePublicKey suite params sk).pkRoot msg))
            sk.pkSeed (derivePublicKey suite params sk).pkRoot
            (thPreHash suite sk.pkSeed (derivePublicKey suite params sk).pkRoot msg) =
          some (leaf, idxs))
    (hLayers : signProductionHypertreeLayers suite params sk
        (derivePublicKey suite params sk).pkRoot
        (thPrfMsg suite sk.skPrf optRand
          (thPreHash suite sk.pkSeed (derivePublicKey suite params sk).pkRoot msg))
        maxGrind 0 leaf
        (computeProductionForsPk suite params sk
          (UInt64.ofNat (leaf / 2 ^ params.subtreeHeight)) (leaf % 2 ^ params.subtreeHeight))
        params.numLayers = some layerSigs) :
    (evalProductionStatelessSign suite params sk msg optRand maxGrind).isSome = true := by
  obtain ⟨hWf, hSt, hLeafLt, hIdxsLen, hIdxsBound⟩ := deriveProductionStatelessInputs_bounds _ _ _ _ _ _ _ _ hD
  obtain ⟨hDPos, _⟩ := params.productionWellFormed_facts hWf
  have hRange : params.productionLeafIdxInRange leaf = true := by
    rw [PqHashParams.productionLeafIdxInRange_eq]
    simp [hSt, hLeafLt]
  obtain ⟨hLsLen, hLsVer⟩ := signProductionHypertreeLayers_sound suite params sk
    (derivePublicKey suite params sk).pkRoot
    (thPrfMsg suite sk.skPrf optRand
      (thPreHash suite sk.pkSeed (derivePublicKey suite params sk).pkRoot msg))
    maxGrind params.numLayers 0 leaf
    (computeProductionForsPk suite params sk
      (UInt64.ofNat (leaf / 2 ^ params.subtreeHeight)) (leaf % 2 ^ params.subtreeHeight))
    layerSigs hDPos hLeafLt hLayers
  unfold evalProductionStatelessSign signProductionHypertreeCore
  have hSeed : (derivePublicKey suite params sk).pkSeed = sk.pkSeed := rfl
  simp only [hSt, hWf, Bool.not_true, Bool.or_self, Bool.false_eq_true, ↓reduceIte, hSeed, hD, hLayers]
  have hVer : verifyProductionPqHashSig suite params (derivePublicKey suite params sk) msg
      { rRand := thPrfMsg suite sk.skPrf optRand
          (thPreHash suite sk.pkSeed (derivePublicKey suite params sk).pkRoot msg)
        msgTswCtr := 0
        leafGlobalIdx := leaf
        forsOpenings := buildProductionForsOpenings suite params sk
          (UInt64.ofNat (leaf / 2 ^ params.subtreeHeight)) (leaf % 2 ^ params.subtreeHeight) idxs
        layerSigs := layerSigs } = true := by
    rw [verifyProductionPqHashSig_eq]
    have hOpsLen : (buildProductionForsOpenings suite params sk
        (UInt64.ofNat (leaf / 2 ^ params.subtreeHeight)) (leaf % 2 ^ params.subtreeHeight) idxs).length =
        params.forsTrees := by simp [buildProductionForsOpenings]
    simp only [hWf, hRange, Bool.not_true, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
      hLsLen, ne_eq, not_true_eq_false, hSt, hOpsLen, hSeed, hD]
    rw [recoverProductionForsPk_buildProductionForsOpenings suite params sk _ _ idxs hIdxsLen hIdxsBound]
    dsimp only
    rw [hLsVer, Nat.zero_add]
    simp [derivePublicKey]
  simp [hVer]

/-- **Production Stateless Leaf-Reuse WOTS+C Determinism
    (`production_stateless_leaf_reuse_identical_wots_chains`)**:
    In stateless mode (`params.statefulJorts = false`), whenever two messages `(msg₁, optRand₁)` and
    `(msg₂, optRand₂)` map under `deriveProductionStatelessInputs` to the same hypertree leaf `leaf`,
    every layer uses `grindTswInternalCounterAux` (`TAG_H_INTERNAL`, zero `rRand` dependence),
    so `sig₁.layerSigs = sig₂.layerSigs` identically! -/
theorem production_stateless_leaf_reuse_identical_wots_chains
    (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey)
    (msg₁ optRand₁ msg₂ optRand₂ : List UInt8) (maxGrind : Nat)
    {sig₁ sig₂ : PqHashSig}
    (hStateless : params.statefulJorts = false)
    (hSign₁ : evalProductionStatelessSign suite params sk msg₁ optRand₁ maxGrind = some sig₁)
    (hSign₂ : evalProductionStatelessSign suite params sk msg₂ optRand₂ maxGrind = some sig₂)
    (hSameLeaf : sig₁.leafGlobalIdx = sig₂.leafGlobalIdx) :
    sig₁.layerSigs = sig₂.layerSigs := by
  have hNoRand : ∀ (r₁ r₂ pkRoot : List UInt8) (rem l g : Nat) (cur : List UInt8),
      signProductionHypertreeLayers suite params sk pkRoot r₁ maxGrind l g cur rem =
      signProductionHypertreeLayers suite params sk pkRoot r₂ maxGrind l g cur rem := by
    intro r₁ r₂ pkRoot rem
    induction rem with
    | zero => intros; rfl
    | succ rem ih =>
      intro l g cur
      rw [signProductionHypertreeLayers_succ, signProductionHypertreeLayers_succ]
      simp only [hStateless, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      cases grindTswInternalCounterAux suite params.w params.ell1 params.targetSum sk.pkSeed pkRoot cur
          (UInt32.ofNat l) (UInt64.ofNat (g / 2 ^ params.subtreeHeight))
          (UInt32.ofNat (g % 2 ^ params.subtreeHeight)) 0 maxGrind with
      | none => rfl
      | some tr =>
        rcases tr with ⟨ctr, dg, hm⟩
        dsimp only
        rw [ih]
  have hUnpack : ∀ (msg optRand : List UInt8) (sig : PqHashSig),
      evalProductionStatelessSign suite params sk msg optRand maxGrind = some sig →
      signProductionHypertreeLayers suite params sk (derivePublicKey suite params sk).pkRoot
        (thPrfMsg suite sk.skPrf optRand
          (thPreHash suite (derivePublicKey suite params sk).pkSeed (derivePublicKey suite params sk).pkRoot msg))
        maxGrind 0 sig.leafGlobalIdx
        (computeProductionForsPk suite params sk
          (UInt64.ofNat (sig.leafGlobalIdx / 2 ^ params.subtreeHeight))
          (sig.leafGlobalIdx % 2 ^ params.subtreeHeight))
        params.numLayers = some sig.layerSigs := by
    intro msg optRand sig hS
    rw [evalProductionStatelessSign_eq] at hS
    cases hWf : params.productionWellFormed
    · simp [hStateless, hWf] at hS
    · simp only [hStateless, hWf, Bool.not_true, Bool.or_self, Bool.false_eq_true, ↓reduceIte] at hS
      cases hD : deriveProductionStatelessInputs suite params
          (thPrfMsg suite sk.skPrf optRand
            (thPreHash suite (derivePublicKey suite params sk).pkSeed (derivePublicKey suite params sk).pkRoot msg))
          (derivePublicKey suite params sk).pkSeed (derivePublicKey suite params sk).pkRoot
          (thPreHash suite (derivePublicKey suite params sk).pkSeed (derivePublicKey suite params sk).pkRoot msg) with
      | none => rw [hD] at hS; cases hS
      | some pr =>
        rcases pr with ⟨leaf, idxs⟩
        rw [hD] at hS
        unfold signProductionHypertreeCore at hS
        simp only [hStateless, Bool.false_eq_true, ↓reduceIte] at hS
        cases hLs : signProductionHypertreeLayers suite params sk (derivePublicKey suite params sk).pkRoot
            (thPrfMsg suite sk.skPrf optRand
              (thPreHash suite (derivePublicKey suite params sk).pkSeed (derivePublicKey suite params sk).pkRoot msg))
            maxGrind 0 leaf
            (computeProductionForsPk suite params sk
              (UInt64.ofNat (leaf / 2 ^ params.subtreeHeight)) (leaf % 2 ^ params.subtreeHeight))
            params.numLayers with
        | none => rw [hLs] at hS; cases hS
        | some ls =>
          rw [hLs] at hS
          dsimp only at hS
          cases hV : verifyProductionPqHashSig suite params (derivePublicKey suite params sk) msg _ with
          | false => rw [hV] at hS; simp at hS
          | true =>
            rw [hV] at hS
            simp only [↓reduceIte, Option.some.injEq] at hS
            subst hS
            exact hLs
  have h1 := hUnpack msg₁ optRand₁ sig₁ hSign₁
  have h2 := hUnpack msg₂ optRand₂ sig₂ hSign₂
  rw [hSameLeaf, hNoRand _
      (thPrfMsg suite sk.skPrf optRand₂
        (thPreHash suite (derivePublicKey suite params sk).pkSeed
          (derivePublicKey suite params sk).pkRoot msg₂))] at h1
  exact Option.some.inj (h1.symm.trans h2)

/-! ### Production Fixed-Layout Wire Serialization (`PqHashSig::to_wire_bytes` / `from_wire_bytes`) -/

private def takeChunks32 : Nat → List UInt8 → Option (List (List UInt8) × List UInt8)
  | 0, bs => some ([], bs)
  | k + 1, bs =>
    if bs.length < 32 then none
    else
      match takeChunks32 k (bs.drop 32) with
      | none => none
      | some (cs, rem) => some (bs.take 32 :: cs, rem)

private def encodeForsOpeningsWire : List ForsTreeOpening → List UInt8
  | [] => []
  | op :: rest => op.secretVal ++ op.authPath.flatten ++ encodeForsOpeningsWire rest

private def parseForsOpeningsWire : Nat → Nat → List UInt8 → Option (List ForsTreeOpening × List UInt8)
  | 0, _, bs => some ([], bs)
  | rem + 1, forsHeight, bs =>
    if bs.length < 32 then none
    else
      let sec := bs.take 32
      match takeChunks32 forsHeight (bs.drop 32) with
      | none => none
      | some (path, bs1) =>
        match parseForsOpeningsWire rem forsHeight bs1 with
        | none => none
        | some (ops, bs2) => some ({ secretVal := sec, authPath := path } :: ops, bs2)

private def encodeLayerSigsWire : List LayerXmssSig → List UInt8
  | [] => []
  | ls :: rest => be 4 ls.tswCtr ++ ls.wotsChains.flatten ++ ls.authPath.flatten ++ encodeLayerSigsWire rest

private def parseLayerSigsWire : Nat → Nat → Nat → List UInt8 → Option (List LayerXmssSig × List UInt8)
  | 0, _, _, bs => some ([], bs)
  | rem + 1, ell1, subtreeHeight, bs =>
    if bs.length < 4 then none
    else
      let ctr := ofBE (bs.take 4)
      match takeChunks32 ell1 (bs.drop 4) with
      | none => none
      | some (chains, bs1) =>
        match takeChunks32 subtreeHeight bs1 with
        | none => none
        | some (path, bs2) =>
          match parseLayerSigsWire rem ell1 subtreeHeight bs2 with
          | none => none
          | some (lsigs, bs3) =>
            some ({ tswCtr := ctr, wotsChains := chains, authPath := path } :: lsigs, bs3)

/-- Encode `PqHashSig` into exact `PQ_WIRE_MAGIC`-prefixed canonical wire bytes matching
    `PqHashSig::to_wire_bytes` (`crates/qsag-core/src/tsw_baggy.rs:1089–1142`). -/
def encodeProductionSigWire (params : PqHashParams) (sig : PqHashSig) : Except FaultStage (List UInt8) :=
  if !params.productionWellFormed || !params.productionLeafIdxInRange sig.leafGlobalIdx then
    .error .signatureFraming
  else if sig.layerSigs.length ≠ params.numLayers then
    .error .layerCountMismatch
  else if sig.rRand.length ≠ 32 || sig.msgTswCtr ≠ 0 then
    .error .signatureFraming
  else if !(if params.statefulJorts then sig.forsOpenings.isEmpty
            else decide (sig.forsOpenings.length = params.forsTrees) &&
                 sig.forsOpenings.all (checkForsOpeningFraming params)) then
    .error .signatureFraming
  else if !(sig.layerSigs.all (fun ls => decide (ls.tswCtr < 2 ^ 32) && checkLayerSigFraming params ls)) then
    .error .signatureFraming
  else
    .ok (pqWireMagic ++ sig.rRand ++ be 4 sig.msgTswCtr ++ be 8 sig.leafGlobalIdx ++
         encodeForsOpeningsWire sig.forsOpenings ++ encodeLayerSigsWire sig.layerSigs)

/-- Decode `PQ_WIRE_MAGIC`-prefixed canonical wire bytes into `PqHashSig`, matching
    `PqHashSig::from_wire_bytes` (`crates/qsag-core/src/tsw_baggy.rs:1145–1239`). -/
def decodeProductionSigWire (params : PqHashParams) (raw : List UInt8) : Except FaultStage PqHashSig :=
  if !params.productionWellFormed then
    .error .signatureFraming
  else if raw.length < 5 || raw.take 5 != pqWireMagic then
    .error .headerMagicOrVersion
  else if raw.length ≠ params.wireSigBytes then
    .error .signatureFraming
  else
    let rRand := (raw.drop 5).take 32
    let msgTswCtr := ofBE ((raw.drop 37).take 4)
    if msgTswCtr ≠ 0 then
      .error .signatureFraming
    else
      let leafGlobalIdx := ofBE ((raw.drop 41).take 8)
      if !params.productionLeafIdxInRange leafGlobalIdx then
        .error .signatureFraming
      else
        let body := raw.drop 49
        let forsCount := if params.statefulJorts then 0 else params.forsTrees
        match parseForsOpeningsWire forsCount params.forsHeight body with
        | none => .error .signatureFraming
        | some (forsOpenings, afterFors) =>
          match parseLayerSigsWire params.numLayers params.ell1 params.subtreeHeight afterFors with
          | none => .error .signatureFraming
          | some (layerSigs, rem) =>
            if !rem.isEmpty then .error .signatureFraming
            else
              .ok { rRand := rRand
                    msgTswCtr := msgTswCtr
                    leafGlobalIdx := leafGlobalIdx
                    forsOpenings := forsOpenings
                    layerSigs := layerSigs }

/-- End-to-end tri-state byte-level production wire verifier. -/
def verifyProductionWireBytes (suite : TweakableHashSuite) (params : PqHashParams)
    (rawPk rawMsg rawSig : List UInt8) : VerifyReply :=
  match parsePublicKeyWire rawPk with
  | .inl stage => .wireMalformed stage
  | .inr pk =>
    match decodeProductionSigWire params rawSig with
    | .error stage => .wireMalformed stage
    | .ok sig =>
      if verifyProductionPqHashSig suite params pk rawMsg sig then .accept else .reject

private theorem flatten_chunks32_len :
    ∀ (cs : List (List UInt8)), (∀ c ∈ cs, c.length = 32) → cs.flatten.length = cs.length * 32
  | [], _ => rfl
  | c :: cs, hAll => by
    have hc := hAll c List.mem_cons_self
    have hRest := flatten_chunks32_len cs (fun x hx => hAll x (List.mem_cons_of_mem c hx))
    simp only [List.flatten_cons, List.length_append, hc, hRest, List.length_cons]
    omega

private theorem takeChunks32_flatten :
    ∀ (cs : List (List UInt8)) (tail : List UInt8),
      (∀ c ∈ cs, c.length = 32) →
      takeChunks32 cs.length (cs.flatten ++ tail) = some (cs, tail)
  | [], tail, _ => rfl
  | c :: cs, tail, hAll => by
    have hc : c.length = 32 := hAll c List.mem_cons_self
    have hRest := takeChunks32_flatten cs tail (fun x hx => hAll x (List.mem_cons_of_mem c hx))
    simp only [List.length_cons, List.flatten_cons, List.append_assoc, takeChunks32]
    have hNotLt : ¬ ((c ++ (cs.flatten ++ tail)).length < 32) := by simp [hc]
    simp only [hNotLt, ↓reduceIte, List.take_left' hc, List.drop_left' hc, hRest]

private theorem parseForsOpeningsWire_encode (forsHeight : Nat) :
    ∀ (ops : List ForsTreeOpening) (tail : List UInt8),
      (∀ op ∈ ops, op.secretVal.length = 32 ∧ op.authPath.length = forsHeight ∧ ∀ s ∈ op.authPath, s.length = 32) →
      (encodeForsOpeningsWire ops).length = ops.length * (32 + forsHeight * 32) ∧
      parseForsOpeningsWire ops.length forsHeight (encodeForsOpeningsWire ops ++ tail) = some (ops, tail)
  | [], tail, _ => ⟨by simp [encodeForsOpeningsWire], rfl⟩
  | op :: rest, tail, hAll => by
    obtain ⟨hSec, hPLen, hP32⟩ := hAll op List.mem_cons_self
    obtain ⟨hRestLen, hRestParse⟩ := parseForsOpeningsWire_encode forsHeight rest tail
      (fun x hx => hAll x (List.mem_cons_of_mem op hx))
    refine ⟨?_, ?_⟩
    · simp only [encodeForsOpeningsWire, List.length_append, hSec, flatten_chunks32_len op.authPath hP32,
        hPLen, hRestLen, List.length_cons, Nat.succ_mul]
      omega
    · simp only [List.length_cons, encodeForsOpeningsWire, List.append_assoc, parseForsOpeningsWire]
      have hNotLt : ¬ ((op.secretVal ++ (op.authPath.flatten ++ (encodeForsOpeningsWire rest ++ tail))).length < 32) := by
        simp [hSec]
      have hChunks := takeChunks32_flatten op.authPath (encodeForsOpeningsWire rest ++ tail) hP32
      rw [hPLen] at hChunks
      simp only [hNotLt, ↓reduceIte, List.take_left' hSec, List.drop_left' hSec, hChunks, hRestParse]

private theorem parseLayerSigsWire_encode (ell1 subtreeHeight : Nat) :
    ∀ (lsigs : List LayerXmssSig) (tail : List UInt8),
      (∀ ls ∈ lsigs, ls.tswCtr < 2 ^ 32 ∧
        ls.wotsChains.length = ell1 ∧ (∀ c ∈ ls.wotsChains, c.length = 32) ∧
        ls.authPath.length = subtreeHeight ∧ (∀ s ∈ ls.authPath, s.length = 32)) →
      (encodeLayerSigsWire lsigs).length = lsigs.length * (4 + ell1 * 32 + subtreeHeight * 32) ∧
      parseLayerSigsWire lsigs.length ell1 subtreeHeight (encodeLayerSigsWire lsigs ++ tail) = some (lsigs, tail)
  | [], tail, _ => ⟨by simp [encodeLayerSigsWire], rfl⟩
  | ls :: rest, tail, hAll => by
    obtain ⟨hCtr, hCLen, hC32, hPLen, hP32⟩ := hAll ls List.mem_cons_self
    obtain ⟨hRestLen, hRestParse⟩ := parseLayerSigsWire_encode ell1 subtreeHeight rest tail
      (fun x hx => hAll x (List.mem_cons_of_mem ls hx))
    have hBe4Len : (be 4 ls.tswCtr).length = 4 := length_be 4 ls.tswCtr
    refine ⟨?_, ?_⟩
    · simp only [encodeLayerSigsWire, List.length_append, hBe4Len,
        flatten_chunks32_len ls.wotsChains hC32, hCLen,
        flatten_chunks32_len ls.authPath hP32, hPLen, hRestLen, List.length_cons, Nat.succ_mul]
      omega
    · simp only [List.length_cons, encodeLayerSigsWire, List.append_assoc, parseLayerSigsWire]
      have hNotLt : ¬ ((be 4 ls.tswCtr ++ (ls.wotsChains.flatten ++ (ls.authPath.flatten ++ (encodeLayerSigsWire rest ++ tail)))).length < 4) := by
        simp [hBe4Len]
      have hCChunks := takeChunks32_flatten ls.wotsChains (ls.authPath.flatten ++ (encodeLayerSigsWire rest ++ tail)) hC32
      rw [hCLen] at hCChunks
      have hPChunks := takeChunks32_flatten ls.authPath (encodeLayerSigsWire rest ++ tail) hP32
      rw [hPLen] at hPChunks
      have hCtrLt256 : ls.tswCtr < 256 ^ 4 := by
        have hEq : (2 : Nat) ^ 32 = 256 ^ 4 := by decide
        exact hEq ▸ hCtr
      simp only [hNotLt, ↓reduceIte, List.take_left' hBe4Len, List.drop_left' hBe4Len,
        ofBE_be hCtrLt256, hCChunks, hPChunks, hRestParse]

/-- **Exact Wire Round-Trip Theorem (`decodeProductionSigWire_encodeProductionSigWire`)**:
    Every byte buffer emitted by `encodeProductionSigWire` has exact length `params.wireSigBytes`
    and decodes via `decodeProductionSigWire` back to the identical `PqHashSig`. -/
theorem decodeProductionSigWire_encodeProductionSigWire
    (params : PqHashParams) (sig : PqHashSig) (raw : List UInt8)
    (hEnc : encodeProductionSigWire params sig = .ok raw) :
    raw.length = params.wireSigBytes ∧
    decodeProductionSigWire params raw = .ok sig := by
  unfold encodeProductionSigWire at hEnc
  cases hWf : params.productionWellFormed
  · simp [hWf] at hEnc
  · cases hRange : params.productionLeafIdxInRange sig.leafGlobalIdx
    · simp [hWf, hRange] at hEnc
    · simp only [hWf, hRange, Bool.not_true, Bool.or_self, Bool.false_eq_true, ↓reduceIte] at hEnc
      by_cases hLsLen : sig.layerSigs.length = params.numLayers
      · simp only [hLsLen, ne_eq, not_true_eq_false, ↓reduceIte] at hEnc
        by_cases hRLen : sig.rRand.length = 32
        · by_cases hCtr0 : sig.msgTswCtr = 0
          · simp only [hRLen, hCtr0, not_true_eq_false, decide_false, Bool.or_self,
              Bool.false_eq_true, ↓reduceIte] at hEnc
            cases hForsOk : (if params.statefulJorts then sig.forsOpenings.isEmpty
                else decide (sig.forsOpenings.length = params.forsTrees) &&
                     sig.forsOpenings.all (checkForsOpeningFraming params))
            · simp [hForsOk] at hEnc
            · simp only [hForsOk, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hEnc
              cases hLayersOk : sig.layerSigs.all (fun ls => decide (ls.tswCtr < 2 ^ 32) && checkLayerSigFraming params ls)
              · simp [hLayersOk] at hEnc
              · simp only [hLayersOk, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at hEnc
                subst hEnc
                have hForsProps :
                    sig.forsOpenings.length = (if params.statefulJorts then 0 else params.forsTrees) ∧
                    ∀ op ∈ sig.forsOpenings, op.secretVal.length = 32 ∧ op.authPath.length = params.forsHeight ∧
                      ∀ s ∈ op.authPath, s.length = 32 := by
                  cases hSt : params.statefulJorts
                  · simp only [hSt, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq,
                      List.all_eq_true, checkForsOpeningFraming] at hForsOk ⊢
                    exact ⟨hForsOk.1, fun op hMem => ⟨hForsOk.2 op hMem |>.1.1, hForsOk.2 op hMem |>.1.2, hForsOk.2 op hMem |>.2⟩⟩
                  · simp only [hSt, ↓reduceIte, List.isEmpty_iff] at hForsOk ⊢
                    rw [hForsOk]; exact ⟨rfl, fun _ h => by cases h⟩
                have hLayerProps :
                    ∀ ls ∈ sig.layerSigs, ls.tswCtr < 2 ^ 32 ∧
                      ls.wotsChains.length = params.ell1 ∧ (∀ c ∈ ls.wotsChains, c.length = 32) ∧
                      ls.authPath.length = params.subtreeHeight ∧ (∀ s ∈ ls.authPath, s.length = 32) := by
                  simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, checkLayerSigFraming] at hLayersOk
                  intro ls hMem
                  have hL := hLayersOk ls hMem
                  exact ⟨hL.1, hL.2.1.1.1, hL.2.1.1.2, hL.2.1.2, hL.2.2⟩
                obtain ⟨hForsByteLen, hForsParse⟩ := parseForsOpeningsWire_encode params.forsHeight
                  sig.forsOpenings (encodeLayerSigsWire sig.layerSigs) hForsProps.2
                obtain ⟨hLayerByteLen, hLayerParse⟩ := parseLayerSigsWire_encode params.ell1 params.subtreeHeight
                  sig.layerSigs [] hLayerProps
                simp only [List.append_nil] at hLayerParse
                have hMagicLen : pqWireMagic.length = 5 := rfl
                have hBe4 : (be 4 0).length = 4 := length_be 4 0
                have hBe8 : (be 8 sig.leafGlobalIdx).length = 8 := length_be 8 _
                have hWireLen :
                    (pqWireMagic ++ sig.rRand ++ be 4 0 ++ be 8 sig.leafGlobalIdx ++
                     encodeForsOpeningsWire sig.forsOpenings ++ encodeLayerSigsWire sig.layerSigs).length =
                    params.wireSigBytes := by
                  rw [PqHashParams.wireSigBytes_eq]
                  simp only [List.length_append, hMagicLen, hRLen, hBe4, hBe8, hForsByteLen,
                    hForsProps.1, hLayerByteLen, hLsLen]
                  cases params.statefulJorts <;> simp <;> omega
                refine ⟨hWireLen, ?_⟩
                unfold decodeProductionSigWire
                have hNotLt5 : ¬ (params.wireSigBytes < 5) := by
                  rw [PqHashParams.wireSigBytes_eq]; dsimp only; omega
                have hAssoc :
                    pqWireMagic ++ sig.rRand ++ be 4 0 ++ be 8 sig.leafGlobalIdx ++
                      encodeForsOpeningsWire sig.forsOpenings ++ encodeLayerSigsWire sig.layerSigs =
                    pqWireMagic ++ (sig.rRand ++ (be 4 0 ++ (be 8 sig.leafGlobalIdx ++
                      (encodeForsOpeningsWire sig.forsOpenings ++ encodeLayerSigsWire sig.layerSigs)))) := by
                  simp only [List.append_assoc]
                have hTakeMagic :
                    (pqWireMagic ++ (sig.rRand ++ (be 4 0 ++ (be 8 sig.leafGlobalIdx ++
                      (encodeForsOpeningsWire sig.forsOpenings ++ encodeLayerSigsWire sig.layerSigs))))).take 5 =
                    pqWireMagic := List.take_left' hMagicLen
                have hLeafLt64 : sig.leafGlobalIdx < 256 ^ 8 := by
                  obtain ⟨_, _, _, _, _, _, _, _, _, hTot62, _, _, _, _⟩ := params.productionWellFormed_facts hWf
                  have hRange' := hRange
                  rw [PqHashParams.productionLeafIdxInRange_eq] at hRange'
                  dsimp only at hRange'
                  have hLtCap : sig.leafGlobalIdx < 2 ^ (if params.statefulJorts && decide (params.maxSigsLog2 < params.numLayers * params.subtreeHeight) then params.maxSigsLog2 else params.numLayers * params.subtreeHeight) :=
                    of_decide_eq_true hRange'
                  have hCapLe62 : (if params.statefulJorts && decide (params.maxSigsLog2 < params.numLayers * params.subtreeHeight) then params.maxSigsLog2 else params.numLayers * params.subtreeHeight) ≤ 62 := by
                    split
                    · rename_i hC; simp only [Bool.and_eq_true, decide_eq_true_eq] at hC; omega
                    · exact hTot62
                  have hPowLe : 2 ^ (if params.statefulJorts && decide (params.maxSigsLog2 < params.numLayers * params.subtreeHeight) then params.maxSigsLog2 else params.numLayers * params.subtreeHeight) ≤ 2 ^ 62 :=
                    Nat.pow_le_pow_right (by decide) hCapLe62
                  have h62Lt : (2 : Nat) ^ 62 < 256 ^ 8 := by decide
                  omega
                rw [hAssoc] at hWireLen ⊢
                have hMagicBne : ((pqWireMagic ++ (sig.rRand ++ (be 4 0 ++ (be 8 sig.leafGlobalIdx ++
                    (encodeForsOpeningsWire sig.forsOpenings ++ encodeLayerSigsWire sig.layerSigs))))).take 5 != pqWireMagic) = false := by
                  rw [hTakeMagic]; decide
                simp only [hWf, Bool.not_true, hWireLen, hNotLt5, decide_false, hMagicBne, Bool.or_self,
                  Bool.false_eq_true, ↓reduceIte, ne_eq, not_true_eq_false]
                have hDrop5 : (pqWireMagic ++ (sig.rRand ++ (be 4 0 ++ (be 8 sig.leafGlobalIdx ++
                    (encodeForsOpeningsWire sig.forsOpenings ++ encodeLayerSigsWire sig.layerSigs))))).drop 5 =
                    sig.rRand ++ (be 4 0 ++ (be 8 sig.leafGlobalIdx ++
                      (encodeForsOpeningsWire sig.forsOpenings ++ encodeLayerSigsWire sig.layerSigs))) :=
                  List.drop_left' hMagicLen
                have hDrop37 : (pqWireMagic ++ (sig.rRand ++ (be 4 0 ++ (be 8 sig.leafGlobalIdx ++
                    (encodeForsOpeningsWire sig.forsOpenings ++ encodeLayerSigsWire sig.layerSigs))))).drop 37 =
                    be 4 0 ++ (be 8 sig.leafGlobalIdx ++
                      (encodeForsOpeningsWire sig.forsOpenings ++ encodeLayerSigsWire sig.layerSigs)) := by
                  rw [show (37 : Nat) = 5 + 32 by rfl, ← List.drop_drop, hDrop5, List.drop_left' hRLen]
                have hDrop41 : (pqWireMagic ++ (sig.rRand ++ (be 4 0 ++ (be 8 sig.leafGlobalIdx ++
                    (encodeForsOpeningsWire sig.forsOpenings ++ encodeLayerSigsWire sig.layerSigs))))).drop 41 =
                    be 8 sig.leafGlobalIdx ++
                      (encodeForsOpeningsWire sig.forsOpenings ++ encodeLayerSigsWire sig.layerSigs) := by
                  rw [show (41 : Nat) = 37 + 4 by rfl, ← List.drop_drop, hDrop37, List.drop_left' hBe4]
                have hDrop49 : (pqWireMagic ++ (sig.rRand ++ (be 4 0 ++ (be 8 sig.leafGlobalIdx ++
                    (encodeForsOpeningsWire sig.forsOpenings ++ encodeLayerSigsWire sig.layerSigs))))).drop 49 =
                    encodeForsOpeningsWire sig.forsOpenings ++ encodeLayerSigsWire sig.layerSigs := by
                  rw [show (49 : Nat) = 41 + 8 by rfl, ← List.drop_drop, hDrop41, List.drop_left' hBe8]
                rw [hDrop37, List.take_left' hBe4]
                have hOfBe0 : ofBE (be 4 0) = 0 := ofBE_be (by decide)
                rw [hOfBe0]
                simp only [not_true_eq_false, ↓reduceIte]
                rw [hDrop41, List.take_left' hBe8, ofBE_be hLeafLt64]
                simp only [hRange, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
                rw [hDrop49, ← hForsProps.1, hForsParse]
                dsimp only
                rw [← hLsLen, hLayerParse]
                simp only [List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
                rw [hDrop5, List.take_left' hRLen]
                cases sig; dsimp only at hCtr0 ⊢; subst hCtr0; rfl
          · simp [hCtr0] at hEnc
        · simp [hRLen] at hEnc
      · simp [hLsLen] at hEnc

/-- Production parameter acceptance, separate from the permissive toy geometry. -/
def ProductionParameterProfile (p : PqHashParams) : Prop := p.productionWellFormed = true

theorem production_profile_covers_full_digest (p : PqHashParams)
    (h : ProductionParameterProfile p) : p.ell1 * Nat.log2 p.w = 256 := by
  simp only [ProductionParameterProfile, PqHashParams.productionWellFormed,
    Bool.and_eq_true, decide_eq_true_eq] at h
  omega

/-! Production checked boundaries. `verifyStatelessChecked` above is the compatibility shim over
`verifyPqHashSig`, kept because `QsagChallenge.lean` freezes its contracts. The production boundary is
`verifyProductionStatelessChecked` / `ValidProductionJortsBatch`; their forgery reductions are
`Qsag.production_checked_stateless_euf_cma_break` and
`Qsag.validProductionJortsBatch_item_forgery_break` in `Qsag.HypertreeEufCma` §7. -/

def verifyProductionStatelessChecked (suite : TweakableHashSuite) (params : PqHashParams)
    (pk : PqPublicKey) (msg : List UInt8) (sig : PqHashSig) : Bool :=
  !params.statefulJorts && verifyProductionPqHashSig suite params pk msg sig

theorem verifyProductionStatelessChecked_sound (suite : TweakableHashSuite) (params : PqHashParams)
    (pk : PqPublicKey) (msg : List UInt8) (sig : PqHashSig)
    (h : verifyProductionStatelessChecked suite params pk msg sig = true) :
    params.statefulJorts = false ∧ verifyProductionPqHashSig suite params pk msg sig = true := by
  cases hs : params.statefulJorts <;> simp_all [verifyProductionStatelessChecked]

/-- V3 batch validation checks the production domain tags and layer digest rules. -/
def ValidProductionJortsBatch (params : PqHashParams) (items : List JortsBatchItem) : Bool :=
  decide (params.statefulJorts = true) &&
  decide (items ≠ []) &&
  decide (items.map (fun item => (item.validatorPk, item.signature.leafGlobalIdx))).Nodup &&
  items.all (fun item => verifyProductionPqHashSig poseidon2Suite params
    item.validatorPk item.message item.signature)

theorem validProductionJortsBatch_sound {params : PqHashParams} {items : List JortsBatchItem}
    (h : ValidProductionJortsBatch params items = true) :
    params.statefulJorts = true ∧ items ≠ [] ∧
    (items.map (fun item => (item.validatorPk, item.signature.leafGlobalIdx))).Nodup ∧
    ∀ item ∈ items, verifyProductionPqHashSig poseidon2Suite params
      item.validatorPk item.message item.signature = true := by
  simp only [ValidProductionJortsBatch, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

/-! ### Exports for lane threshold-a -/

theorem computeProductionForsPk_def (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (tree0 : UInt64) (kp0 : Nat) :
    computeProductionForsPk suite params sk tree0 kp0 = (
  let kpU32 := UInt32.ofNat kp0
  let roots := (List.range params.forsTrees).map fun j =>
    computeMerkleNodeKp suite sk.pkSeed 0 tree0 .forsTree kpU32
      (forsIndexedLeafFn suite sk tree0 kp0 j) params.forsHeight j 0
  thTweakTl suite sk.pkSeed ⟨0, tree0, .forsRoots, kpU32, 0, 0⟩ roots
  ) := by rfl

theorem buildProductionForsOpenings_def (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (tree0 : UInt64) (kp0 : Nat) (idxs : List Nat) :
    buildProductionForsOpenings suite params sk tree0 kp0 idxs = (
  let kpU32 := UInt32.ofNat kp0
  (List.range params.forsTrees).map fun j =>
    let idxJ := idxs.getD j 0
    { secretVal := forsIndexedSecretLeaf suite sk tree0 kp0 j idxJ
      authPath  := buildMerkleAuthPathKp suite sk.pkSeed 0 tree0 .forsTree kpU32
                     (forsIndexedLeafFn suite sk tree0 kp0 j) params.forsHeight j 0 idxJ }
  ) := by rfl

theorem signProductionHypertreeCore_def (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (pk : PqPublicKey) (msg mu rRand : List UInt8)
    (leafGlobalIdx : Nat) (forsIdxs : Option (List Nat)) (maxGrind : Nat) :
    signProductionHypertreeCore suite params sk pk msg mu rRand leafGlobalIdx forsIdxs maxGrind = (
  let subLeaves := 2 ^ params.subtreeHeight
  match (if params.statefulJorts then some ([], mu)
         else
           match forsIdxs with
           | none => none
           | some idxs =>
             let kp0 := leafGlobalIdx % subLeaves
             let tree0 := UInt64.ofNat (leafGlobalIdx / subLeaves)
             some (buildProductionForsOpenings suite params sk tree0 kp0 idxs,
                   computeProductionForsPk suite params sk tree0 kp0)) with
  | none => none
  | some (forsOpenings, curRoot) =>
    match signProductionHypertreeLayers suite params sk pk.pkRoot rRand maxGrind 0 leafGlobalIdx curRoot params.numLayers with
    | none => none
    | some layerSigs =>
      let sig : PqHashSig :=
        { rRand := rRand
          msgTswCtr := 0
          leafGlobalIdx := leafGlobalIdx
          forsOpenings := forsOpenings
          layerSigs := layerSigs }
      if verifyProductionPqHashSig suite params pk msg sig then some sig else none
  ) := by rfl

theorem evalProductionStatelessSign_def (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (msg optRand : List UInt8) (maxGrind : Nat) :
    evalProductionStatelessSign suite params sk msg optRand maxGrind = (
  if params.statefulJorts || !params.productionWellFormed then none
  else
    let pk := derivePublicKey suite params sk
    let mu := thPreHash suite pk.pkSeed pk.pkRoot msg
    let rRand := thPrfMsg suite sk.skPrf optRand mu
    match deriveProductionStatelessInputs suite params rRand pk.pkSeed pk.pkRoot mu with
    | none => none
    | some (leafGlobalIdx, forsIdxs) =>
      signProductionHypertreeCore suite params sk pk msg mu rRand leafGlobalIdx (some forsIdxs) maxGrind
  ) := by rfl

theorem evalProductionStatefulSign_def (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (msg optRand : List UInt8) (epoch maxGrind : Nat) :
    evalProductionStatefulSign suite params sk msg optRand epoch maxGrind = (
  if !params.statefulJorts || !params.productionWellFormed || !params.productionLeafIdxInRange epoch then none
  else
    let pk := derivePublicKey suite params sk
    let mu := thPreHash suite pk.pkSeed pk.pkRoot msg
    let rRand := thPrfMsg suite sk.skPrf optRand mu
    signProductionHypertreeCore suite params sk pk msg mu rRand epoch none maxGrind
  ) := by rfl

end Qsag
end
