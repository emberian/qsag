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
import all Qsag.Oracle.Keccak
public import Qsag.Oracle.Poseidon2
public import Qsag.Oracle.UcGames

import Qsag.Tactic.AssuranceKit

public section
namespace Qsag

set_option autoImplicit false

/-! ## 1. Pre-Locked 32-Byte Big-Endian `HashAdrs` Framing (`encodeAdrs_injective`) -/

/-- Domain-separation role of a 32-byte hash address inside the hypertree / FORS / WOTS+C hierarchy. -/
inductive AdrsKind where
  | wotsHash | wotsPk | tree | forsTree | forsRoots | wotsPrf | forsPrf
  deriving DecidableEq, Repr, Inhabited

/-- Canonical 32-bit wire tag for `AdrsKind`. -/
def AdrsKind.toCode : AdrsKind → UInt32
  | .wotsHash => 0 | .wotsPk => 1 | .tree => 2 | .forsTree => 3
  | .forsRoots => 4 | .wotsPrf => 5 | .forsPrf => 6

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

private def thXofMsgBlocks (suite : TweakableHashSuite) (rRand pkSeed pkRoot mu : List UInt8)
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

/-- Permissive small-`ell1` fast model test profiles (rejected by `productionWellFormed`). -/
def compactTestParams        : PqHashParams := ⟨4, 8, 2, 2, 4, 2, 4, false⟩
def compactJortsParams       : PqHashParams := ⟨4, 8, 2, 1, 0, 0, 2, true⟩

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

def walkMerkleAuthPath (suite : TweakableHashSuite) (pkSeed : List UInt8)
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

