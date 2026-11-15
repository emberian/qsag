module
public import Qsag.Protocol.Signing.ProdCollisionLayers
import all Qsag.Protocol.Signing.ProdCollisionLayers
import all Qsag.Protocol.Signing.ProdCollisionWitness
import all Qsag.Protocol.Signing.HypertreeEufCma
import all Qsag.Protocol.Signing.HashSigs
import Qsag.Tactic.AssuranceKit

/-!
# Qsag.Protocol.Signing.ProdCollisionExtraction — the production forgery reduction as a function

`production_forgery_extract` maps an accepted production signature on an unsigned message to a
`ProdBreakWitness`: the FORS index-coverage event, a returned `ProdTcrWitness`, or the preimage
event. It follows the same traversal as `production_forgery_break_of_signingLog`, with every case
split made on decidable data, so the collision it returns is the one the verifier walk meets.

`ProdCollisionEvents` runs it on game outcomes and `ProdCollisionAccounting` enumerates the
candidate targets of one forgery.

Scope. Deterministic extraction only: no probability is assigned to any branch, the hash is not
modelled as an oracle, and no running time is given for the extractor. The index-coverage and
preimage events stay propositions tied to the forgery; only the branch taken is data.
-/

public section
namespace Qsag

set_option autoImplicit false

/-! Local abbreviations for positions on the verification path of `sigStar`. They are unhygienic
notations: each expands in place to the term on its right, over the `suite`, `params`, `sk`,
`msgStar`, `sigStar` (and, for `digs⟪i⟫`, `cur`) in scope. -/

-- Hypertree position of the path at layer `i`.
set_option hygiene false in
local notation:max "pos⟪" i "⟫" => sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight)
-- Tree address of the path at layer `i`.
set_option hygiene false in
local notation:max "tree⟪" i "⟫" =>
  UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) / 2 ^ params.subtreeHeight)
-- Key-pair (leaf) index of the path at layer `i`.
set_option hygiene false in
local notation:max "kp⟪" i "⟫" =>
  (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) % 2 ^ params.subtreeHeight)
-- Layer-`i` XMSS signature of the forgery.
set_option hygiene false in
local notation:max "lsig⟪" i "⟫" => (sigStar.layerSigs.getD i ⟨0, [], []⟩)
-- Honest public root.
set_option hygiene false in
local notation:max "PK_ROOT" => (derivePublicKey suite params sk).pkRoot
-- Root of the top subtree, as the verifier walk reaches it.
set_option hygiene false in
local notation:max "TOP_ROOT" =>
  (computeXmssSubtreeRoot suite params sk (UInt32.ofNat (params.numLayers - 1))
    (UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ (params.numLayers * params.subtreeHeight))))
-- FORS tree address, key pair and leaf indices of the forgery.
set_option hygiene false in
local notation:max "FORS_TREE" => (UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ params.subtreeHeight))
set_option hygiene false in
local notation:max "FORS_KP" => (sigStar.leafGlobalIdx % 2 ^ params.subtreeHeight)
set_option hygiene false in
local notation:max "FORS_IDXS" =>
  (prodSigForsIdxs suite params (derivePublicKey suite params sk) msgStar sigStar)

/-! ### FORS -/

/-- `prod_forsRoots_meet_honest` as a function. -/
def prodForsRootsExtract (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey)
    (tree0 : UInt64) (kp0 : Nat) (idxs : List Nat) (ops : List ForsTreeOpening) (C : Type)
    (mkCol : ∀ (j h d b : Nat) (x y : List UInt8),
      j < params.forsTrees → d + (h + 1) = params.forsHeight →
      b * 2 ^ (h + 1) ≤ idxs.getD j 0 → idxs.getD j 0 < (b + 1) * 2 ^ (h + 1) →
      thPreimage tagThH sk.pkSeed
          ⟨0, tree0, .forsTree, UInt32.ofNat kp0, UInt32.ofNat (h + 1),
            UInt32.ofNat (j * 2 ^ d + b)⟩ [x, y] ≠
        thPreimage tagThH sk.pkSeed
          ⟨0, tree0, .forsTree, UInt32.ofNat kp0, UInt32.ofNat (h + 1),
            UInt32.ofNat (j * 2 ^ d + b)⟩
          [computeMerkleNodeKp suite sk.pkSeed 0 tree0 .forsTree (UInt32.ofNat kp0)
             (forsIndexedLeafFn suite sk tree0 kp0 j) h (2 * (j * 2 ^ d + b)) (2 * b),
           computeMerkleNodeKp suite sk.pkSeed 0 tree0 .forsTree (UInt32.ofNat kp0)
             (forsIndexedLeafFn suite sk tree0 kp0 j) h (2 * (j * 2 ^ d + b) + 1) (2 * b + 1)] →
      suite.rawHash
          (thPreimage tagThH sk.pkSeed
            ⟨0, tree0, .forsTree, UInt32.ofNat kp0, UInt32.ofNat (h + 1),
              UInt32.ofNat (j * 2 ^ d + b)⟩ [x, y]) =
        suite.rawHash
          (thPreimage tagThH sk.pkSeed
            ⟨0, tree0, .forsTree, UInt32.ofNat kp0, UInt32.ofNat (h + 1),
              UInt32.ofNat (j * 2 ^ d + b)⟩
            [computeMerkleNodeKp suite sk.pkSeed 0 tree0 .forsTree (UInt32.ofNat kp0)
               (forsIndexedLeafFn suite sk tree0 kp0 j) h (2 * (j * 2 ^ d + b)) (2 * b),
             computeMerkleNodeKp suite sk.pkSeed 0 tree0 .forsTree (UInt32.ofNat kp0)
               (forsIndexedLeafFn suite sk tree0 kp0 j) h (2 * (j * 2 ^ d + b) + 1)
               (2 * b + 1)]) → C)
    (hIdxs : ∀ J, J < params.forsTrees → idxs.getD J 0 < 2 ^ params.forsHeight) :
    ∀ (rem j : Nat) (rootsF : List (List UInt8)),
      j + rem ≤ params.forsTrees →
      recoverProductionForsTreeRoots suite params sk.pkSeed tree0 kp0 idxs ops j rem = some rootsF →
      rootsF = (List.range rem).map (fun off =>
        computeMerkleNodeKp suite sk.pkSeed 0 tree0 .forsTree (UInt32.ofNat kp0)
          (forsIndexedLeafFn suite sk tree0 kp0 (j + off)) params.forsHeight (j + off) 0) →
      PSum (∀ off, off < rem →
        forsIndexedLeafHash suite sk.pkSeed tree0 kp0 (j + off) (idxs.getD (j + off) 0)
          (ops.getD (j + off) ⟨[], []⟩).secretVal =
        forsIndexedLeafFn suite sk tree0 kp0 (j + off) (idxs.getD (j + off) 0)) C
  | 0, _, _, _, _, _ => .inl (fun off h => absurd h (Nat.not_lt_zero off))
  | rem + 1, j, rootsF, hB, hRec, hEq =>
    have hj : j < params.forsTrees :=
      Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (Nat.succ_pos rem)) hB
    have hInv := prod_recoverForsTreeRoots_succ_inv suite params sk.pkSeed tree0 kp0 idxs ops j rem
      rootsF hRec
    match hWalk : walkMerkleAuthPathKp suite sk.pkSeed 0 tree0 .forsTree (UInt32.ofNat kp0)
        params.forsHeight j (idxs.getD j 0)
        (forsIndexedLeafHash suite sk.pkSeed tree0 kp0 j (idxs.getD j 0)
          (ops.getD j ⟨[], []⟩).secretVal)
        (ops.getD j ⟨[], []⟩).authPath with
    | none => False.elim (by
        obtain ⟨rJ, _, hW, _, _⟩ := hInv
        rw [hWalk] at hW
        cases hW)
    | some rJ =>
      match hRest : recoverProductionForsTreeRoots suite params sk.pkSeed tree0 kp0 idxs ops
          (j + 1) rem with
      | none => False.elim (by
          obtain ⟨_, rs, _, hR, _⟩ := hInv
          rw [hRest] at hR
          cases hR)
      | some rsF =>
        have hSplit :
            rJ = computeMerkleNodeKp suite sk.pkSeed 0 tree0 .forsTree (UInt32.ofNat kp0)
              (forsIndexedLeafFn suite sk tree0 kp0 j) params.forsHeight j 0 ∧
            rsF = (List.range rem).map (fun off =>
              computeMerkleNodeKp suite sk.pkSeed 0 tree0 .forsTree (UInt32.ofNat kp0)
                (forsIndexedLeafFn suite sk tree0 kp0 (j + 1 + off)) params.forsHeight
                (j + 1 + off) 0) := by
          obtain ⟨rJ', rs', hW, hR, hRoots⟩ := hInv
          rw [hWalk] at hW
          rw [hRest] at hR
          have h1 : rJ = rJ' := Option.some.inj hW
          have h2 : rsF = rs' := Option.some.inj hR
          rw [hRoots, ← h1, ← h2, prod_list_range_succ_shift] at hEq
          simp only [Nat.add_zero, List.cons.injEq] at hEq
          refine ⟨hEq.1, ?_⟩
          rw [hEq.2]
          apply List.map_congr_left
          intro off _
          rw [show j + (off + 1) = j + 1 + off by omega]
        have hj0 : j * 2 ^ 0 + 0 = j := by rw [Nat.pow_zero, Nat.mul_one, Nat.add_zero]
        match prodWalkMerkleKpExtract suite sk.pkSeed 0 tree0 .forsTree (UInt32.ofNat kp0)
            (forsIndexedLeafFn suite sk tree0 kp0 j) j (idxs.getD j 0) params.forsHeight C
            (fun h d b x y hD hLo hHi hNe hHash => mkCol j h d b x y hj hD hLo hHi hNe hHash)
            params.forsHeight 0 0 (idxs.getD j 0)
            (forsIndexedLeafHash suite sk.pkSeed tree0 kp0 j (idxs.getD j 0)
              (ops.getD j ⟨[], []⟩).secretVal)
            (ops.getD j ⟨[], []⟩).authPath (Nat.zero_add _) (hIdxs j hj)
            (by rw [Nat.zero_mul, Nat.zero_add])
            (by rw [hj0, ← hSplit.1]; exact hWalk) with
        | .inr c => .inr c
        | .inl hLeaf =>
          match prodForsRootsExtract suite params sk tree0 kp0 idxs ops C mkCol hIdxs rem (j + 1)
              rsF (by omega) hRest hSplit.2 with
          | .inr c => .inr c
          | .inl hAll =>
            .inl (fun off hoff => by
              cases off with
              | zero =>
                rw [Nat.add_zero]
                exact hLeaf
              | succ off' =>
                have h := hAll off' (by omega)
                rw [show j + 1 + off' = j + (off' + 1) by omega] at h
                exact h)

/-- Outcome of the production reduction on one accepted forgery. -/
inductive ProdBreakWitness (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey)
    (log : List (List UInt8 × PqHashSig)) (msgStar : List UInt8) (sigStar : PqHashSig) : Type where
  | itsr (h : ProdForsItsrBreak suite params (derivePublicKey suite params sk) log msgStar sigStar)
  | tcr (w : ProdTcrWitness suite params sk log msgStar sigStar)
  | pre (h : ProdPreimageBreak suite params sk log msgStar sigStar)

/-- `prod_fors_break` as a function. -/
def prodForsExtract (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey)
    (log : List (List UInt8 × PqHashSig)) (msgStar : List UInt8) (sigStar : PqHashSig)
    (hStateless : params.statefulJorts = false)
    (hTrees : 0 < params.forsTrees) (hFresh : ∀ e ∈ log, e.1 ≠ msgStar)
    (hLenI : (FORS_IDXS).length = params.forsTrees)
    (hBnd : ∀ idx ∈ (FORS_IDXS), idx < 2 ^ params.forsHeight)
    (hRec : recoverProductionForsPk suite params sk.pkSeed FORS_TREE FORS_KP (FORS_IDXS)
        sigStar.forsOpenings =
      some (computeProductionForsPk suite params sk FORS_TREE FORS_KP)) :
    ProdBreakWitness suite params sk log msgStar sigStar :=
  have hInv := prod_recoverForsPk_some_inv suite params sk.pkSeed FORS_TREE FORS_KP (FORS_IDXS)
    sigStar.forsOpenings _ hRec
  match hRoots : recoverProductionForsTreeRoots suite params sk.pkSeed FORS_TREE FORS_KP (FORS_IDXS)
      sigStar.forsOpenings 0 params.forsTrees with
  | none => False.elim (by
      obtain ⟨r, hr, _⟩ := hInv
      rw [hRoots] at hr
      cases hr)
  | some rootsF =>
    have hPkEq :
        thCall suite tagThTl sk.pkSeed ⟨0, FORS_TREE, .forsRoots, UInt32.ofNat FORS_KP, 0, 0⟩
            rootsF =
        thCall suite tagThTl sk.pkSeed ⟨0, FORS_TREE, .forsRoots, UInt32.ofNat FORS_KP, 0, 0⟩
          ((List.range params.forsTrees).map fun j =>
            computeMerkleNodeKp suite sk.pkSeed 0 FORS_TREE .forsTree (UInt32.ofNat FORS_KP)
              (forsIndexedLeafFn suite sk FORS_TREE FORS_KP j) params.forsHeight j 0) := by
      obtain ⟨r, hr, hpk⟩ := hInv
      rw [hRoots] at hr
      have hrEq : rootsF = r := Option.some.inj hr
      rw [← hrEq, computeProductionForsPk_eq] at hpk
      dsimp only at hpk
      rw [thTweakTl_eq, thTweakTl_eq] at hpk
      exact hpk.symm
    match prodThCallSplit suite hPkEq with
    | .inr ⟨hNe, hHash⟩ => .tcr ⟨.forsRoots, _, hStateless, ⟨_, rfl⟩, hNe, hHash⟩
    | .inl hArgs =>
      have hIdxs : ∀ J, J < params.forsTrees → (FORS_IDXS).getD J 0 < 2 ^ params.forsHeight := by
        intro J hJ
        have hJLen : J < (FORS_IDXS).length := by rw [hLenI]; exact hJ
        rw [list_getD_eq_getElem _ 0 hJLen]
        exact hBnd _ (List.getElem_mem hJLen)
      match prodForsRootsExtract suite params sk FORS_TREE FORS_KP (FORS_IDXS) sigStar.forsOpenings
          (ProdTcrWitness suite params sk log msgStar sigStar)
          (fun j h d b x y hj hD hLo hHi hNe hHash =>
            ⟨.forsNode j h d b, _, ⟨hStateless, hj, hD, hLo, hHi⟩, ⟨x, y, rfl⟩, hNe, hHash⟩)
          hIdxs params.forsTrees 0 rootsF (by omega) hRoots
          (by
            rw [hArgs]
            apply List.map_congr_left
            intro off _
            rw [Nat.zero_add]) with
      | .inr w => .tcr w
      | .inl hAll =>
        match prodBoundedSearch
            (fun j => (sigStar.leafGlobalIdx, j, (FORS_IDXS).getD j 0) ∉
              prodLogForsLeaves suite params (derivePublicKey suite params sk) log)
            (fun j =>
              if h : (sigStar.leafGlobalIdx, j, (FORS_IDXS).getD j 0) ∈
                  prodLogForsLeaves suite params (derivePublicKey suite params sk) log then
                .inr (fun hn => hn h)
              else .inl h) params.forsTrees with
        | .inl ⟨j, ⟨hj, hUn⟩⟩ =>
          .pre (by
            have h := hAll j hj
            rw [Nat.zero_add] at h
            exact ProdPreimageBreak.fors j hj hUn h)
        | .inr hCov =>
          .itsr ⟨hFresh, hTrees, by
            intro a ha
            unfold prodSigForsLeaves at ha
            obtain ⟨j, hj, hEq⟩ := List.mem_map.mp ha
            rw [← hEq]
            exact Decidable.of_not_not (hCov j (List.mem_range.mp hj))⟩

/-! ### Extraction from the production signing log -/

/-- **Stateful production profiles.** The accepted forgery yields a returned collision on its
    verification path (including a collision on the message pre-hash) or the WOTS preimage
    event. -/
def production_stateful_forgery_extract (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (queries : List ProdSigningQuery) (msgStar : List UInt8) (sigStar :
        PqHashSig)
    (hw : params.w = 4 ∨ params.w = 16) (hStateful : params.statefulJorts = true)
    (hOneTime : ∀ q, q ∈ queries → ∀ q', q' ∈ queries → q.epoch = q'.epoch → q = q')
    (hFresh : ∀ e ∈ productionSigningLog suite params sk queries, e.1 ≠ msgStar)
    (hAccept : verifyProductionPqHashSig suite params (derivePublicKey suite params sk) msgStar
      sigStar = true) :
    PSum (ProdTcrWitness suite params sk (productionSigningLog suite params sk queries) msgStar
        sigStar)
      (ProdPreimageBreak suite params sk (productionSigningLog suite params sk queries) msgStar
        sigStar) :=
  have hLog := fun e he => productionSigningLog_entryOk suite params sk queries e he
  have hCons := productionSigningLog_consistent suite params sk queries (fun _ => hOneTime)
  have hInv := verifyProductionPqHashSig_stateful_inv suite params _ msgStar sigStar hStateful
      hAccept
  have hNe : sigStar.layerSigs ≠ [] := by
    obtain ⟨hPwf, hLen, _, _⟩ := hInv
    obtain ⟨hDPos, _⟩ := params.productionWellFormed_facts hPwf
    intro hnil
    rw [hnil, List.length_nil] at hLen
    omega
  have hVer : verifyProductionHypertreeLayers suite params sk.pkSeed PK_ROOT sigStar.rRand 0
      (pos⟪0⟫)
      (thPreHash suite sk.pkSeed PK_ROOT msgStar) sigStar.layerSigs = some TOP_ROOT := by
    obtain ⟨_, _, hLt, hHt⟩ := hInv
    have h0 : pos⟪0⟫ = sigStar.leafGlobalIdx := by
      simp only [Nat.zero_mul, Nat.pow_zero, Nat.div_one]
    have hTop : PK_ROOT = TOP_ROOT := by
      rw [Nat.div_eq_of_lt hLt]
      rfl
    rw [h0, ← hTop]
    exact hHt
  match prodHypertreeWalkExtract suite params sk (productionSigningLog suite params sk queries)
      msgStar sigStar hw hInv.1 hLog hCons sigStar.layerSigs 0 _ hNe
      (fun j => by rw [Nat.zero_add]) (by rw [Nat.zero_add]; exact hInv.2.1) hVer with
  | .tcr w => .inl w
  | .pre h => .inr h
  | .honest e he _ hEq =>
    have hMu :
        thCall suite tagHPre sk.pkSeed zeroAdrs [PK_ROOT, msgStar] =
        thCall suite tagHPre sk.pkSeed zeroAdrs [PK_ROOT, e.1] := by
      have h := hEq
      unfold prodHonestLayerMsg at h
      simp only [hStateful, ↓reduceIte] at h
      rw [thPreHash_eq, thPreHash_eq] at h
      exact h
    match prodThCallSplit suite hMu with
    | .inl hArgs => False.elim (by
        simp only [List.cons.injEq, and_true] at hArgs
        exact hFresh e he hArgs.2.symm)
    | .inr ⟨hNe', hHash⟩ => .inl ⟨.preHash e, _, ⟨he, hStateful⟩, rfl, hNe', hHash⟩

/-- **Stateless production profiles.** -/
def production_stateless_forgery_extract (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (queries : List ProdSigningQuery) (msgStar : List UInt8) (sigStar :
        PqHashSig)
    (hw : params.w = 4 ∨ params.w = 16) (hStateless : params.statefulJorts = false)
    (hFresh : ∀ e ∈ productionSigningLog suite params sk queries, e.1 ≠ msgStar)
    (hAccept : verifyProductionPqHashSig suite params (derivePublicKey suite params sk) msgStar
      sigStar = true) :
    ProdBreakWitness suite params sk (productionSigningLog suite params sk queries) msgStar
      sigStar :=
  have hLog := fun e he => productionSigningLog_entryOk suite params sk queries e he
  have hCons := productionSigningLog_consistent suite params sk queries
    (fun hSt => by rw [hStateless] at hSt; cases hSt)
  have hFacts := prod_stateless_accept_facts suite params sk msgStar sigStar hStateless hAccept
  have hPwf := hFacts.1
  have hTrees := (params.productionWellFormed_stateless_fors hPwf hStateless).1
  have hNe : sigStar.layerSigs ≠ [] := by
    obtain ⟨hDPos, _⟩ := params.productionWellFormed_facts hPwf
    have hLen := hFacts.2.1
    intro hnil
    rw [hnil, List.length_nil] at hLen
    omega
  match hFors : recoverProductionForsPk suite params sk.pkSeed FORS_TREE FORS_KP (FORS_IDXS)
      sigStar.forsOpenings with
  | none => False.elim (by
      obtain ⟨_, _, _, _, _, f, hF, _⟩ := hFacts
      rw [hFors] at hF
      cases hF)
  | some forsPkF =>
    have hVer : verifyProductionHypertreeLayers suite params sk.pkSeed PK_ROOT sigStar.rRand 0
        (pos⟪0⟫)
        forsPkF sigStar.layerSigs = some TOP_ROOT := by
      obtain ⟨_, _, hLt, _, _, f, hF, hHt⟩ := hFacts
      rw [hFors] at hF
      have hf : forsPkF = f := Option.some.inj hF
      have h0 : pos⟪0⟫ = sigStar.leafGlobalIdx := by
        simp only [Nat.zero_mul, Nat.pow_zero, Nat.div_one]
      have hTop : PK_ROOT = TOP_ROOT := by
        rw [Nat.div_eq_of_lt hLt]
        rfl
      rw [h0, ← hTop, hf]
      exact hHt
    match prodHypertreeWalkExtract suite params sk (productionSigningLog suite params sk queries)
        msgStar sigStar hw hPwf hLog hCons sigStar.layerSigs 0 forsPkF hNe
        (fun j => by rw [Nat.zero_add]) (by rw [Nat.zero_add]; exact hFacts.2.1) hVer with
    | .tcr w => .tcr w
    | .pre h => .pre h
    | .honest e _ hPos hEq =>
      prodForsExtract suite params sk (productionSigningLog suite params sk queries) msgStar
        sigStar hStateless hTrees hFresh hFacts.2.2.2.1 hFacts.2.2.2.2.1 (by
          have hL : e.2.leafGlobalIdx = sigStar.leafGlobalIdx := by
            simpa only [Nat.zero_mul, Nat.pow_zero, Nat.div_one] using hPos
          have hForsEq : forsPkF = computeProductionForsPk suite params sk FORS_TREE FORS_KP := by
            rw [hEq]
            unfold prodHonestLayerMsg
            simp only [hStateless, ↓reduceIte, Bool.false_eq_true, hL]
          rw [← hForsEq]
          exact hFors)

/-- **Both production modes.** -/
def production_forgery_extract (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (queries : List ProdSigningQuery) (msgStar : List UInt8) (sigStar :
        PqHashSig)
    (hw : params.w = 4 ∨ params.w = 16)
    (hOneTime : params.statefulJorts = true →
      ∀ q, q ∈ queries → ∀ q', q' ∈ queries → q.epoch = q'.epoch → q = q')
    (hFresh : ∀ e ∈ productionSigningLog suite params sk queries, e.1 ≠ msgStar)
    (hAccept : verifyProductionPqHashSig suite params (derivePublicKey suite params sk) msgStar
      sigStar = true) :
    ProdBreakWitness suite params sk (productionSigningLog suite params sk queries) msgStar
      sigStar :=
  match hSt : params.statefulJorts with
  | false =>
    production_stateless_forgery_extract suite params sk queries msgStar sigStar hw hSt hFresh
      hAccept
  | true =>
    match production_stateful_forgery_extract suite params sk queries msgStar sigStar hw hSt
        (hOneTime hSt) hFresh hAccept with
    | .inl w => .tcr w
    | .inr h => .pre h

/-! ### Statements about the returned witness -/

theorem ProdBreakWitness.toBreak {suite : TweakableHashSuite} {params : PqHashParams}
    {sk : PqSecretKey} {log : List (List UInt8 × PqHashSig)} {msgStar : List UInt8}
    {sigStar : PqHashSig} (b : ProdBreakWitness suite params sk log msgStar sigStar) :
    ProdForsItsrBreak suite params (derivePublicKey suite params sk) log msgStar sigStar ∨
    ProdSmTcrBreak suite params sk log ∨ ProdPreimageBreak suite params sk log msgStar sigStar :=
  match b with
  | .itsr h => .inl h
  | .tcr w => .inr (.inl w.toSmTcrBreak)
  | .pre h => .inr (.inr h)

/-- **Stateful production forgery: returned collision or preimage.** Strengthens
    `production_stateful_forgery_break`: the collision branch is a `ProdTcrWitness` for this
    forgery, not the unrestricted `ProdSmTcrBreak`. -/
theorem production_stateful_forgery_witness (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (queries : List ProdSigningQuery) (msgStar : List UInt8) (sigStar :
        PqHashSig)
    (hw : params.w = 4 ∨ params.w = 16) (hStateful : params.statefulJorts = true)
    (hOneTime : ∀ q, q ∈ queries → ∀ q', q' ∈ queries → q.epoch = q'.epoch → q = q')
    (hFresh : ∀ e ∈ productionSigningLog suite params sk queries, e.1 ≠ msgStar)
    (hAccept : verifyProductionPqHashSig suite params (derivePublicKey suite params sk) msgStar
      sigStar = true) :
    Nonempty (ProdTcrWitness suite params sk (productionSigningLog suite params sk queries)
      msgStar sigStar) ∨
    ProdPreimageBreak suite params sk (productionSigningLog suite params sk queries) msgStar
      sigStar :=
  match production_stateful_forgery_extract suite params sk queries msgStar sigStar hw hStateful
      hOneTime hFresh hAccept with
  | .inl w => .inl ⟨w⟩
  | .inr h => .inr h

/-- **Production forgery, both modes: index coverage, returned collision or preimage.** -/
theorem production_forgery_witness (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (queries : List ProdSigningQuery) (msgStar : List UInt8) (sigStar :
        PqHashSig)
    (hw : params.w = 4 ∨ params.w = 16)
    (hOneTime : params.statefulJorts = true →
      ∀ q, q ∈ queries → ∀ q', q' ∈ queries → q.epoch = q'.epoch → q = q')
    (hFresh : ∀ e ∈ productionSigningLog suite params sk queries, e.1 ≠ msgStar)
    (hAccept : verifyProductionPqHashSig suite params (derivePublicKey suite params sk) msgStar
      sigStar = true) :
    ProdForsItsrBreak suite params (derivePublicKey suite params sk)
      (productionSigningLog suite params sk queries) msgStar sigStar ∨
    Nonempty (ProdTcrWitness suite params sk (productionSigningLog suite params sk queries)
      msgStar sigStar) ∨
    ProdPreimageBreak suite params sk (productionSigningLog suite params sk queries) msgStar
      sigStar :=
  match production_forgery_extract suite params sk queries msgStar sigStar hw hOneTime hFresh
      hAccept with
  | .itsr h => .inl h
  | .tcr w => .inr (.inl ⟨w⟩)
  | .pre h => .inr (.inr h)

/-- The existing existential statement `production_forgery_break_of_signingLog` is the image of
    the extractor output under `ProdBreakWitness.toBreak`. -/
theorem production_forgery_break_via_extract (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (queries : List ProdSigningQuery) (msgStar : List UInt8) (sigStar :
        PqHashSig)
    (hw : params.w = 4 ∨ params.w = 16)
    (hOneTime : params.statefulJorts = true →
      ∀ q, q ∈ queries → ∀ q', q' ∈ queries → q.epoch = q'.epoch → q = q')
    (hFresh : ∀ e ∈ productionSigningLog suite params sk queries, e.1 ≠ msgStar)
    (hAccept : verifyProductionPqHashSig suite params (derivePublicKey suite params sk) msgStar
      sigStar = true) :
    ProdForsItsrBreak suite params (derivePublicKey suite params sk)
      (productionSigningLog suite params sk queries) msgStar sigStar ∨
    ProdSmTcrBreak suite params sk (productionSigningLog suite params sk queries) ∨
    ProdPreimageBreak suite params sk (productionSigningLog suite params sk queries) msgStar
      sigStar :=
  (production_forgery_extract suite params sk queries msgStar sigStar hw hOneTime hFresh
    hAccept).toBreak

/-- **Production checked stateless boundary: index coverage, returned collision or preimage.** -/
theorem production_checked_stateless_forgery_witness (suite : TweakableHashSuite)
    (params : PqHashParams) (sk : PqSecretKey) (queries : List ProdSigningQuery)
    (msgStar : List UInt8) (sigStar : PqHashSig) (hw : params.w = 4 ∨ params.w = 16)
    (hFresh : ∀ e ∈ productionSigningLog suite params sk queries, e.1 ≠ msgStar)
    (hAccept : verifyProductionStatelessChecked suite params (derivePublicKey suite params sk)
      msgStar sigStar = true) :
    ProdForsItsrBreak suite params (derivePublicKey suite params sk)
      (productionSigningLog suite params sk queries) msgStar sigStar ∨
    Nonempty (ProdTcrWitness suite params sk (productionSigningLog suite params sk queries)
      msgStar sigStar) ∨
    ProdPreimageBreak suite params sk (productionSigningLog suite params sk queries) msgStar
      sigStar := by
  obtain ⟨hSt, hVer⟩ := verifyProductionStatelessChecked_sound suite params _ msgStar sigStar
      hAccept
  exact production_forgery_witness suite params sk queries msgStar sigStar hw
    (fun hT => by rw [hSt] at hT; cases hT) hFresh hVer

/-- **`ValidProductionJortsBatch` item: returned collision or preimage.** -/
theorem validProductionJortsBatch_item_forgery_witness (params : PqHashParams)
    (items : List JortsBatchItem) (hValid : ValidProductionJortsBatch params items = true)
    (item : JortsBatchItem) (hItem : item ∈ items)
    (sk : PqSecretKey) (queries : List ProdSigningQuery)
    (hPk : item.validatorPk = derivePublicKey poseidon2Suite params sk)
    (hw : params.w = 4 ∨ params.w = 16)
    (hOneTime : ∀ q, q ∈ queries → ∀ q', q' ∈ queries → q.epoch = q'.epoch → q = q')
    (hFresh : ∀ e ∈ productionSigningLog poseidon2Suite params sk queries, e.1 ≠ item.message) :
    Nonempty (ProdTcrWitness poseidon2Suite params sk
      (productionSigningLog poseidon2Suite params sk queries) item.message item.signature) ∨
    ProdPreimageBreak poseidon2Suite params sk
      (productionSigningLog poseidon2Suite params sk queries) item.message item.signature := by
  obtain ⟨hSt, _, _, hAll⟩ := validProductionJortsBatch_sound hValid
  have hAcc := hAll item hItem
  rw [hPk] at hAcc
  exact production_stateful_forgery_witness poseidon2Suite params sk queries item.message
    item.signature hw hSt hOneTime hFresh hAcc

/-- On the concrete accepted toy forgery the extractor output is inhabited. -/
theorem production_forgery_witness_inhabited :
    Nonempty (ProdTcrWitness crumbToySuite prodToyStatefulParams ⟨[], [], []⟩ [] []
      prodToyForgery) ∨
    ProdPreimageBreak crumbToySuite prodToyStatefulParams ⟨[], [], []⟩ [] [] prodToyForgery :=
  production_stateful_forgery_witness crumbToySuite prodToyStatefulParams ⟨[], [], []⟩ [] []
    prodToyForgery (.inl rfl) rfl (fun _ h => by cases h) (fun _ h => by cases h)
    prodToyForgery_accepted

end Qsag
end

#verify_constructive Qsag.ProdBreakWitness.toBreak
#verify_constructive Qsag.production_stateful_forgery_witness Qsag.production_forgery_witness
#verify_constructive Qsag.validProductionJortsBatch_item_forgery_witness
#verify_constructive Qsag.production_forgery_break_via_extract
#verify_constructive Qsag.production_checked_stateless_forgery_witness
#verify_inhabited Qsag.production_stateful_forgery_witness Qsag.witness_production_stateful_forgery
