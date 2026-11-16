module
public import Qsag.Protocol.Signing.HypertreeEufCma
import Qsag.Tactic.AssuranceKit

/-!
# Qsag.Protocol.Signing.ProdCollisionWitness — returned collision witnesses for the production verifier

`ProdSmTcrBreak` (in `HypertreeEufCma`) is an existential `Prop` over every honest hash input of
the key, with unbounded tree and chain indices and no reference to the forged signature. This
module supplies the data that an extractor returns instead:

* `ProdTargetIdx` names an honest hash input *relative to the hypertree leaf of the forgery*. The
  tree and key-pair addresses are not free: `ProdTargetIdx.input` computes them from that leaf.
* `ProdTargetIdx.OnPath` bounds every remaining index and pins Merkle nodes to the authentication
  path of the forgery (`n * 2 ^ (h + 1) ≤ leafIdx < (n + 1) * 2 ^ (h + 1)`), so a forgery
  determines a list of candidate targets of explicit size (`ProdCollisionAccounting`).
* `ProdTargetIdx.ForgedCall` records that the colliding input is the input of the hash call the
  verifier makes at that same address while checking the forgery.
* `ProdTcrWitness` packages target, colliding input and the three facts, in `Type`.

The generic walkers `prodWalkMerkleExtract`, `prodWalkMerkleKpExtract`, `prodChainExtract` and
`prodAllChainsExtract` are the `PSum`-valued counterparts of `walkMerkle_meets_honest`,
`walkMerkleKp_meets_honest` and `wotsChain_meets_honest_gen`. They return the collision found
along the traversal together with its position facts; nothing is obtained by eliminating an
existential.

Scope. These are deterministic extraction statements. They do not bound the probability of the
returned collision, and they do not model the hash as an oracle.
-/

public section
namespace Qsag

set_option autoImplicit false

/-! ### Constructive case splits -/

/-- Two tweakable-hash calls under the same tag, seed and address with equal outputs have equal
    arguments or exhibit a raw collision. The split is made on the arguments, so evaluating it
    never inspects the tag or the address. -/
def prodThCallSplit (suite : TweakableHashSuite)
    {t p : List UInt8} {a : HashAdrs} {xs₁ xs₂ : List (List UInt8)}
    (hEq : thCall suite t p a xs₁ = thCall suite t p a xs₂) :
    PSum (xs₁ = xs₂)
         (thPreimage t p a xs₁ ≠ thPreimage t p a xs₂ ∧
          suite.rawHash (thPreimage t p a xs₁) = suite.rawHash (thPreimage t p a xs₂)) :=
  if hArgs : xs₁ = xs₂ then
    .inl hArgs
  else
    .inr ⟨fun hPre => hArgs (thPreimage_injective hPre).2.2.2,
      by rw [← thCall_eq, ← thCall_eq]; exact hEq⟩

def prodBoundedSearch (p : Nat → Prop) (hDec : ∀ i, PSum (p i) (¬ p i)) :
    (n : Nat) → PSum { i : Nat // i < n ∧ p i } (∀ i, i < n → ¬ p i)
  | 0 => .inr (fun i hi => absurd hi (Nat.not_lt_zero i))
  | n + 1 =>
    match prodBoundedSearch p hDec n with
    | .inl ⟨i, hi, hp⟩ => .inl ⟨i, ⟨Nat.lt_succ_of_lt hi, hp⟩⟩
    | .inr hNone =>
      match hDec n with
      | .inl hp => .inl ⟨n, ⟨Nat.lt_succ_self n, hp⟩⟩
      | .inr hn => .inr (fun i hi => by
          rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hlt | heq
          · exact hNone i hlt
          · rw [heq]; exact hn)

def prodListSearch {α : Type} (p : α → Prop) (hDec : ∀ a, PSum (p a) (¬ p a)) :
    (l : List α) → PSum { a : α // a ∈ l ∧ p a } (∀ a, a ∈ l → ¬ p a)
  | [] => .inr (fun _ h => by cases h)
  | x :: xs =>
    match hDec x with
    | .inl hp => .inl ⟨x, ⟨List.mem_cons_self, hp⟩⟩
    | .inr hn =>
      match prodListSearch p hDec xs with
      | .inl ⟨a, ⟨ha, hp⟩⟩ => .inl ⟨a, ⟨List.mem_cons_of_mem x ha, hp⟩⟩
      | .inr hNone => .inr (fun a ha => by
          rcases List.mem_cons.mp ha with heq | hTl
          · rw [heq]; exact hn
          · exact hNone a hTl)

/-! ### Honest targets addressed from the leaf of the forgery -/

/-- An honest hash input on the verification path of a signature with hypertree leaf `leaf`.
    Tree and key-pair addresses are computed from `leaf` by `ProdTargetIdx.input`. -/
inductive ProdTargetIdx : Type where
  /-- XMSS node at height `h + 1`, index `n`, in the layer-`layer` subtree on the path. -/
  | xmssNode (layer h n : Nat)
  /-- WOTS public-key compression of the layer-`layer` key on the path. -/
  | wotsPk (layer : Nat)
  /-- Chain step `step → step + 1` of chain `r` of the layer-`layer` key on the path. -/
  | chainStep (layer r step : Nat)
  /-- FORS tree `j`, node at height `h + 1` with local index `b`; its address index is
      `j * 2 ^ d + b`. -/
  | forsNode (j h d b : Nat)
  /-- FORS root compression at the leaf. -/
  | forsRoots
  /-- Layer-`i` digest input of the logged signature `e`. -/
  | signedDigest (e : List UInt8 × PqHashSig) (i : Nat)
  /-- Message pre-hash input of the logged signature `e`. -/
  | preHash (e : List UInt8 × PqHashSig)

/-- Honest hash input named by a target index. -/
def ProdTargetIdx.input (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey)
    (leaf : Nat) : ProdTargetIdx → List UInt8
  | .xmssNode layer h n =>
    thPreimage tagThH sk.pkSeed
      ⟨UInt32.ofNat layer,
       UInt64.ofNat (leaf / 2 ^ (layer * params.subtreeHeight) / 2 ^ params.subtreeHeight),
       .tree, 0, UInt32.ofNat (h + 1), UInt32.ofNat n⟩
      [computeMerkleNode suite sk.pkSeed (UInt32.ofNat layer)
         (UInt64.ofNat (leaf / 2 ^ (layer * params.subtreeHeight) / 2 ^ params.subtreeHeight)) .tree
         (computeWotsPk suite params sk (UInt32.ofNat layer)
           (UInt64.ofNat (leaf / 2 ^ (layer * params.subtreeHeight) / 2 ^ params.subtreeHeight)))
         h (2 * n),
       computeMerkleNode suite sk.pkSeed (UInt32.ofNat layer)
         (UInt64.ofNat (leaf / 2 ^ (layer * params.subtreeHeight) / 2 ^ params.subtreeHeight)) .tree
         (computeWotsPk suite params sk (UInt32.ofNat layer)
           (UInt64.ofNat (leaf / 2 ^ (layer * params.subtreeHeight) / 2 ^ params.subtreeHeight)))
         h (2 * n + 1)]
  | .wotsPk layer =>
    thPreimage tagThTl sk.pkSeed
      ⟨UInt32.ofNat layer,
       UInt64.ofNat (leaf / 2 ^ (layer * params.subtreeHeight) / 2 ^ params.subtreeHeight),
       .wotsPk,
       UInt32.ofNat (leaf / 2 ^ (layer * params.subtreeHeight) % 2 ^ params.subtreeHeight), 0, 0⟩
      ((List.range params.ell1).map fun r =>
        honestChainNode suite sk (UInt32.ofNat layer)
          (UInt64.ofNat (leaf / 2 ^ (layer * params.subtreeHeight) / 2 ^ params.subtreeHeight))
          (leaf / 2 ^ (layer * params.subtreeHeight) % 2 ^ params.subtreeHeight) r (params.w - 1))
  | .chainStep layer r step =>
    thPreimage tagThF sk.pkSeed
      ⟨UInt32.ofNat layer,
       UInt64.ofNat (leaf / 2 ^ (layer * params.subtreeHeight) / 2 ^ params.subtreeHeight),
       .wotsHash,
       UInt32.ofNat (leaf / 2 ^ (layer * params.subtreeHeight) % 2 ^ params.subtreeHeight),
       UInt32.ofNat r, UInt32.ofNat step⟩
      [honestChainNode suite sk (UInt32.ofNat layer)
        (UInt64.ofNat (leaf / 2 ^ (layer * params.subtreeHeight) / 2 ^ params.subtreeHeight))
        (leaf / 2 ^ (layer * params.subtreeHeight) % 2 ^ params.subtreeHeight) r step]
  | .forsNode j h d b =>
    thPreimage tagThH sk.pkSeed
      ⟨0, UInt64.ofNat (leaf / 2 ^ params.subtreeHeight), .forsTree,
       UInt32.ofNat (leaf % 2 ^ params.subtreeHeight), UInt32.ofNat (h + 1),
       UInt32.ofNat (j * 2 ^ d + b)⟩
      [computeMerkleNodeKp suite sk.pkSeed 0 (UInt64.ofNat (leaf / 2 ^ params.subtreeHeight))
         .forsTree (UInt32.ofNat (leaf % 2 ^ params.subtreeHeight))
         (forsIndexedLeafFn suite sk (UInt64.ofNat (leaf / 2 ^ params.subtreeHeight))
           (leaf % 2 ^ params.subtreeHeight) j) h (2 * (j * 2 ^ d + b)) (2 * b),
       computeMerkleNodeKp suite sk.pkSeed 0 (UInt64.ofNat (leaf / 2 ^ params.subtreeHeight))
         .forsTree (UInt32.ofNat (leaf % 2 ^ params.subtreeHeight))
         (forsIndexedLeafFn suite sk (UInt64.ofNat (leaf / 2 ^ params.subtreeHeight))
           (leaf % 2 ^ params.subtreeHeight) j) h (2 * (j * 2 ^ d + b) + 1) (2 * b + 1)]
  | .forsRoots =>
    thPreimage tagThTl sk.pkSeed
      ⟨0, UInt64.ofNat (leaf / 2 ^ params.subtreeHeight), .forsRoots,
       UInt32.ofNat (leaf % 2 ^ params.subtreeHeight), 0, 0⟩
      ((List.range params.forsTrees).map fun j =>
        computeMerkleNodeKp suite sk.pkSeed 0 (UInt64.ofNat (leaf / 2 ^ params.subtreeHeight))
          .forsTree (UInt32.ofNat (leaf % 2 ^ params.subtreeHeight))
          (forsIndexedLeafFn suite sk (UInt64.ofNat (leaf / 2 ^ params.subtreeHeight))
            (leaf % 2 ^ params.subtreeHeight) j) params.forsHeight j 0)
  | .signedDigest e i =>
    prodLayerPreimage params e.2.rRand sk.pkSeed (derivePublicKey suite params sk).pkRoot
      (prodHonestLayerMsg suite params sk e i) i
      (UInt64.ofNat (e.2.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) / 2 ^ params.subtreeHeight))
      (UInt32.ofNat (e.2.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) % 2 ^ params.subtreeHeight))
      (e.2.layerSigs.getD i ⟨0, [], []⟩).tswCtr
  | .preHash e =>
    thPreimage tagHPre sk.pkSeed zeroAdrs [(derivePublicKey suite params sk).pkRoot, e.1]

theorem ProdTargetIdx.input_xmssNode (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (leaf : Nat) (layer : Nat) (h : Nat) (n : Nat) :
    (ProdTargetIdx.xmssNode layer h n).input suite params sk leaf =
    thPreimage tagThH sk.pkSeed
      ⟨UInt32.ofNat layer,
       UInt64.ofNat (leaf / 2 ^ (layer * params.subtreeHeight) / 2 ^ params.subtreeHeight),
       .tree, 0, UInt32.ofNat (h + 1), UInt32.ofNat n⟩
      [computeMerkleNode suite sk.pkSeed (UInt32.ofNat layer)
         (UInt64.ofNat (leaf / 2 ^ (layer * params.subtreeHeight) / 2 ^ params.subtreeHeight)) .tree
         (computeWotsPk suite params sk (UInt32.ofNat layer)
           (UInt64.ofNat (leaf / 2 ^ (layer * params.subtreeHeight) / 2 ^ params.subtreeHeight)))
         h (2 * n),
       computeMerkleNode suite sk.pkSeed (UInt32.ofNat layer)
         (UInt64.ofNat (leaf / 2 ^ (layer * params.subtreeHeight) / 2 ^ params.subtreeHeight)) .tree
         (computeWotsPk suite params sk (UInt32.ofNat layer)
           (UInt64.ofNat (leaf / 2 ^ (layer * params.subtreeHeight) / 2 ^ params.subtreeHeight)))
         h (2 * n + 1)] := by
  rfl

theorem ProdTargetIdx.input_wotsPk (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (leaf : Nat) (layer : Nat) :
    (ProdTargetIdx.wotsPk layer).input suite params sk leaf =
    thPreimage tagThTl sk.pkSeed
      ⟨UInt32.ofNat layer,
       UInt64.ofNat (leaf / 2 ^ (layer * params.subtreeHeight) / 2 ^ params.subtreeHeight),
       .wotsPk,
       UInt32.ofNat (leaf / 2 ^ (layer * params.subtreeHeight) % 2 ^ params.subtreeHeight), 0, 0⟩
      ((List.range params.ell1).map fun r =>
        honestChainNode suite sk (UInt32.ofNat layer)
          (UInt64.ofNat (leaf / 2 ^ (layer * params.subtreeHeight) / 2 ^ params.subtreeHeight))
          (leaf / 2 ^ (layer * params.subtreeHeight) % 2 ^ params.subtreeHeight) r (params.w - 1)) := by
  rfl

theorem ProdTargetIdx.input_chainStep (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (leaf : Nat) (layer : Nat) (r : Nat) (step : Nat) :
    (ProdTargetIdx.chainStep layer r step).input suite params sk leaf =
    thPreimage tagThF sk.pkSeed
      ⟨UInt32.ofNat layer,
       UInt64.ofNat (leaf / 2 ^ (layer * params.subtreeHeight) / 2 ^ params.subtreeHeight),
       .wotsHash,
       UInt32.ofNat (leaf / 2 ^ (layer * params.subtreeHeight) % 2 ^ params.subtreeHeight),
       UInt32.ofNat r, UInt32.ofNat step⟩
      [honestChainNode suite sk (UInt32.ofNat layer)
        (UInt64.ofNat (leaf / 2 ^ (layer * params.subtreeHeight) / 2 ^ params.subtreeHeight))
        (leaf / 2 ^ (layer * params.subtreeHeight) % 2 ^ params.subtreeHeight) r step] := by
  rfl

theorem ProdTargetIdx.input_forsNode (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (leaf : Nat) (j : Nat) (h : Nat) (d : Nat) (b : Nat) :
    (ProdTargetIdx.forsNode j h d b).input suite params sk leaf =
    thPreimage tagThH sk.pkSeed
      ⟨0, UInt64.ofNat (leaf / 2 ^ params.subtreeHeight), .forsTree,
       UInt32.ofNat (leaf % 2 ^ params.subtreeHeight), UInt32.ofNat (h + 1),
       UInt32.ofNat (j * 2 ^ d + b)⟩
      [computeMerkleNodeKp suite sk.pkSeed 0 (UInt64.ofNat (leaf / 2 ^ params.subtreeHeight))
         .forsTree (UInt32.ofNat (leaf % 2 ^ params.subtreeHeight))
         (forsIndexedLeafFn suite sk (UInt64.ofNat (leaf / 2 ^ params.subtreeHeight))
           (leaf % 2 ^ params.subtreeHeight) j) h (2 * (j * 2 ^ d + b)) (2 * b),
       computeMerkleNodeKp suite sk.pkSeed 0 (UInt64.ofNat (leaf / 2 ^ params.subtreeHeight))
         .forsTree (UInt32.ofNat (leaf % 2 ^ params.subtreeHeight))
         (forsIndexedLeafFn suite sk (UInt64.ofNat (leaf / 2 ^ params.subtreeHeight))
           (leaf % 2 ^ params.subtreeHeight) j) h (2 * (j * 2 ^ d + b) + 1) (2 * b + 1)] := by
  rfl

theorem ProdTargetIdx.input_forsRoots (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (leaf : Nat)  :
    (ProdTargetIdx.forsRoots).input suite params sk leaf =
    thPreimage tagThTl sk.pkSeed
      ⟨0, UInt64.ofNat (leaf / 2 ^ params.subtreeHeight), .forsRoots,
       UInt32.ofNat (leaf % 2 ^ params.subtreeHeight), 0, 0⟩
      ((List.range params.forsTrees).map fun j =>
        computeMerkleNodeKp suite sk.pkSeed 0 (UInt64.ofNat (leaf / 2 ^ params.subtreeHeight))
          .forsTree (UInt32.ofNat (leaf % 2 ^ params.subtreeHeight))
          (forsIndexedLeafFn suite sk (UInt64.ofNat (leaf / 2 ^ params.subtreeHeight))
            (leaf % 2 ^ params.subtreeHeight) j) params.forsHeight j 0) := by
  rfl

theorem ProdTargetIdx.input_signedDigest (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (leaf : Nat) (e : List UInt8 × PqHashSig) (i : Nat) :
    (ProdTargetIdx.signedDigest e i).input suite params sk leaf =
    prodLayerPreimage params e.2.rRand sk.pkSeed (derivePublicKey suite params sk).pkRoot
      (prodHonestLayerMsg suite params sk e i) i
      (UInt64.ofNat (e.2.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) / 2 ^ params.subtreeHeight))
      (UInt32.ofNat (e.2.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) % 2 ^ params.subtreeHeight))
      (e.2.layerSigs.getD i ⟨0, [], []⟩).tswCtr := by
  rfl

theorem ProdTargetIdx.input_preHash (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (leaf : Nat) (e : List UInt8 × PqHashSig) :
    (ProdTargetIdx.preHash e).input suite params sk leaf =
    thPreimage tagHPre sk.pkSeed zeroAdrs [(derivePublicKey suite params sk).pkRoot, e.1] := by
  rfl

/-- Index bounds and path provenance of a target, for a forgery with hypertree leaf `leaf` and
    FORS leaf indices `idxs` over the signing log `log`. -/
@[expose, reducible] def ProdTargetIdx.OnPath (params : PqHashParams) (log : List (List UInt8 × PqHashSig))
    (leaf : Nat) (idxs : List Nat) : ProdTargetIdx → Prop
  | .xmssNode layer h n =>
    layer < params.numLayers ∧ h + 1 ≤ params.subtreeHeight ∧
    n * 2 ^ (h + 1) ≤ leaf / 2 ^ (layer * params.subtreeHeight) % 2 ^ params.subtreeHeight ∧
    leaf / 2 ^ (layer * params.subtreeHeight) % 2 ^ params.subtreeHeight < (n + 1) * 2 ^ (h + 1)
  | .wotsPk layer => layer < params.numLayers
  | .chainStep layer r step =>
    layer < params.numLayers ∧ r < params.ell1 ∧ step + 1 ≤ params.w - 1
  | .forsNode j h d b =>
    params.statefulJorts = false ∧ j < params.forsTrees ∧ d + (h + 1) = params.forsHeight ∧
    b * 2 ^ (h + 1) ≤ idxs.getD j 0 ∧ idxs.getD j 0 < (b + 1) * 2 ^ (h + 1)
  | .forsRoots => params.statefulJorts = false
  | .signedDigest e i =>
    e ∈ log ∧ i < params.numLayers ∧
    e.2.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) = leaf / 2 ^ (i * params.subtreeHeight)
  | .preHash e => e ∈ log ∧ params.statefulJorts = true

/-- The colliding input is the input of the hash call that the verifier evaluates, at the address
    of the target, while checking `(msgStar, sigStar)`. Node, chain and compression calls share
    the full tweak of the target. The digest call shares layer, tree and key pair and carries the
    randomness and counter of the forgery. The pre-hash call is the one on `msgStar`. -/
@[expose, reducible] def ProdTargetIdx.ForgedCall (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (msgStar : List UInt8) (sigStar : PqHashSig) :
    ProdTargetIdx → List UInt8 → Prop
  | .xmssNode layer h n, forged =>
    ∃ a b, forged = thPreimage tagThH sk.pkSeed
      ⟨UInt32.ofNat layer,
       UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ (layer * params.subtreeHeight) /
         2 ^ params.subtreeHeight),
       .tree, 0, UInt32.ofNat (h + 1), UInt32.ofNat n⟩ [a, b]
  | .wotsPk layer, forged =>
    ∃ xs, forged = thPreimage tagThTl sk.pkSeed
      ⟨UInt32.ofNat layer,
       UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ (layer * params.subtreeHeight) /
         2 ^ params.subtreeHeight),
       .wotsPk,
       UInt32.ofNat (sigStar.leafGlobalIdx / 2 ^ (layer * params.subtreeHeight) %
         2 ^ params.subtreeHeight), 0, 0⟩ xs
  | .chainStep layer r step, forged =>
    ∃ x, forged = thPreimage tagThF sk.pkSeed
      ⟨UInt32.ofNat layer,
       UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ (layer * params.subtreeHeight) /
         2 ^ params.subtreeHeight),
       .wotsHash,
       UInt32.ofNat (sigStar.leafGlobalIdx / 2 ^ (layer * params.subtreeHeight) %
         2 ^ params.subtreeHeight),
       UInt32.ofNat r, UInt32.ofNat step⟩ [x]
  | .forsNode j h d b, forged =>
    ∃ x y, forged = thPreimage tagThH sk.pkSeed
      ⟨0, UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ params.subtreeHeight), .forsTree,
       UInt32.ofNat (sigStar.leafGlobalIdx % 2 ^ params.subtreeHeight), UInt32.ofNat (h + 1),
       UInt32.ofNat (j * 2 ^ d + b)⟩ [x, y]
  | .forsRoots, forged =>
    ∃ xs, forged = thPreimage tagThTl sk.pkSeed
      ⟨0, UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ params.subtreeHeight), .forsRoots,
       UInt32.ofNat (sigStar.leafGlobalIdx % 2 ^ params.subtreeHeight), 0, 0⟩ xs
  | .signedDigest _ i, forged =>
    ∃ cur, forged = prodLayerPreimage params sigStar.rRand sk.pkSeed
      (derivePublicKey suite params sk).pkRoot cur i
      (UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) /
        2 ^ params.subtreeHeight))
      (UInt32.ofNat (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) %
        2 ^ params.subtreeHeight))
      (sigStar.layerSigs.getD i ⟨0, [], []⟩).tswCtr
  | .preHash _, forged =>
    forged = thPreimage tagHPre sk.pkSeed zeroAdrs
      [(derivePublicKey suite params sk).pkRoot, msgStar]

/-- **Returned target collision.** A collision with an honest hash input on the verification path
    of `(msgStar, sigStar)`: the target index, the colliding input, the bounds and path position of
    the target, the verifier call the colliding input belongs to, and the collision itself. -/
structure ProdTcrWitness (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey)
    (log : List (List UInt8 × PqHashSig)) (msgStar : List UInt8) (sigStar : PqHashSig) : Type where
  target : ProdTargetIdx
  forged : List UInt8
  onPath : target.OnPath params log sigStar.leafGlobalIdx
    (prodSigForsIdxs suite params (derivePublicKey suite params sk) msgStar sigStar)
  call : target.ForgedCall suite params sk msgStar sigStar forged
  ne : forged ≠ target.input suite params sk sigStar.leafGlobalIdx
  collides : suite.rawHash forged =
    suite.rawHash (target.input suite params sk sigStar.leafGlobalIdx)

/-- Every indexed target is one of the honest inputs classified by `ProdHonestHashTarget`. -/
theorem ProdTargetIdx.input_honest (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (log : List (List UInt8 × PqHashSig)) (leaf : Nat) (idxs : List Nat) :
    ∀ t : ProdTargetIdx, t.OnPath params log leaf idxs →
      ProdHonestHashTarget suite params sk log (t.input suite params sk leaf)
  | .xmssNode layer h n, _ => .xmssNode (UInt32.ofNat layer) _ h n
  | .wotsPk layer, _ => .wotsPk (UInt32.ofNat layer) _ _
  | .chainStep layer r step, _ => .chainStep (UInt32.ofNat layer) _ _ r step
  | .forsNode j h d b, _ => .forsNode _ _ j h (j * 2 ^ d + b) b
  | .forsRoots, _ => .forsRoots _ _
  | .signedDigest e i, hOn => .signedDigest e hOn.1 i hOn.2.1
  | .preHash e, hOn => .preHash e hOn.1

/-- A returned collision witnesses the existential compatibility event. -/
theorem ProdTcrWitness.toSmTcrBreak {suite : TweakableHashSuite} {params : PqHashParams}
    {sk : PqSecretKey} {log : List (List UInt8 × PqHashSig)} {msgStar : List UInt8}
    {sigStar : PqHashSig} (w : ProdTcrWitness suite params sk log msgStar sigStar) :
    ProdSmTcrBreak suite params sk log :=
  ProdSmTcrBreak.mk _ w.forged
    (ProdTargetIdx.input_honest suite params sk log _ _ w.target w.onPath) w.ne w.collides

/-- Executable collision check: the winning predicate of a target-collision game whose challenger
    holds the honest input named by `target`. -/
def prodTcrCheck (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey)
    (leaf : Nat) (target : ProdTargetIdx) (forged : List UInt8) : Bool :=
  decide (forged ≠ target.input suite params sk leaf) &&
  decide (suite.rawHash forged = suite.rawHash (target.input suite params sk leaf))

theorem prodTcrCheck_eq (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey)
    (leaf : Nat) (target : ProdTargetIdx) (forged : List UInt8) :
    prodTcrCheck suite params sk leaf target forged =
      (decide (forged ≠ target.input suite params sk leaf) &&
        decide (suite.rawHash forged = suite.rawHash (target.input suite params sk leaf))) := by
  rfl

theorem ProdTcrWitness.check {suite : TweakableHashSuite} {params : PqHashParams}
    {sk : PqSecretKey} {log : List (List UInt8 × PqHashSig)} {msgStar : List UInt8}
    {sigStar : PqHashSig} (w : ProdTcrWitness suite params sk log msgStar sigStar) :
    prodTcrCheck suite params sk sigStar.leafGlobalIdx w.target w.forged = true := by
  unfold prodTcrCheck
  rw [Bool.and_eq_true]
  exact ⟨decide_eq_true w.ne, decide_eq_true w.collides⟩

/-! ### Traversals that return the collision -/

/-- `walkMerkle_meets_honest` returning the collision. `U` is the leaf index of the walk and `H`
    the height it started from; the callback receives the two children the verifier hashed and the
    position of the node on the path to `U`. -/
@[expose] def prodWalkMerkleExtract (suite : TweakableHashSuite) (pkSeed : List UInt8)
    (layer : UInt32) (tree : UInt64) (kind : AdrsKind) (leafFn : Nat → List UInt8)
    (U H : Nat) (C : Type)
    (mkCol : ∀ (h n : Nat) (a b : List UInt8),
      h + 1 ≤ H → n * 2 ^ (h + 1) ≤ U → U < (n + 1) * 2 ^ (h + 1) →
      thPreimage tagThH pkSeed ⟨layer, tree, kind, 0, UInt32.ofNat (h + 1), UInt32.ofNat n⟩ [a, b] ≠
        thPreimage tagThH pkSeed ⟨layer, tree, kind, 0, UInt32.ofNat (h + 1), UInt32.ofNat n⟩
          [computeMerkleNode suite pkSeed layer tree kind leafFn h (2 * n),
           computeMerkleNode suite pkSeed layer tree kind leafFn h (2 * n + 1)] →
      suite.rawHash
          (thPreimage tagThH pkSeed ⟨layer, tree, kind, 0, UInt32.ofNat (h + 1), UInt32.ofNat n⟩
            [a, b]) =
        suite.rawHash
          (thPreimage tagThH pkSeed ⟨layer, tree, kind, 0, UInt32.ofNat (h + 1), UInt32.ofNat n⟩
            [computeMerkleNode suite pkSeed layer tree kind leafFn h (2 * n),
             computeMerkleNode suite pkSeed layer tree kind leafFn h (2 * n + 1)]) → C) :
    ∀ (h nodeIdx localIdx : Nat) (leaf : List UInt8) (path : List (List UInt8)),
      h ≤ H → localIdx < 2 ^ h → nodeIdx * 2 ^ h + localIdx = U →
      walkMerkleAuthPath suite pkSeed layer tree kind h nodeIdx localIdx leaf path =
        some (computeMerkleNode suite pkSeed layer tree kind leafFn h nodeIdx) →
      PSum (leaf = leafFn U) C
  | 0, nodeIdx, localIdx, leaf, path, _, hLt, hU, hW =>
    match path, hW with
    | [], hW => .inl (by
        simp only [walkMerkleAuthPath, computeMerkleNode_zero, Option.some.injEq] at hW
        have h0 : localIdx = 0 := by rw [Nat.pow_zero] at hLt; omega
        rw [h0, Nat.pow_zero, Nat.mul_one, Nat.add_zero] at hU
        rw [← hU]; exact hW)
    | _ :: _, hW => False.elim (by simp [walkMerkleAuthPath] at hW)
  | h + 1, nodeIdx, localIdx, leaf, path, hLe, hLt, hU, hW =>
    match path, hW with
    | [], hW => False.elim (by simp [walkMerkleAuthPath] at hW)
    | sib :: rest, hW =>
      have hMul : nodeIdx * 2 ^ (h + 1) = (2 * nodeIdx) * 2 ^ h := by
        rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm (nodeIdx * 2 ^ h) 2, Nat.mul_assoc]
      have hLo : nodeIdx * 2 ^ (h + 1) ≤ U := by rw [← hU]; exact Nat.le_add_right _ _
      have hHi : U < (nodeIdx + 1) * 2 ^ (h + 1) := by
        rw [← hU, Nat.add_mul, Nat.one_mul]; exact Nat.add_lt_add_left hLt _
      if hHalf : localIdx < 2 ^ h then
        match hSub : walkMerkleAuthPath suite pkSeed layer tree kind h (2 * nodeIdx) localIdx
            leaf rest with
        | none =>
          False.elim (by simp only [walkMerkleAuthPath, hHalf, ↓reduceIte, hSub] at hW; cases hW)
        | some sub =>
          have hCallEq :
              thCall suite tagThH pkSeed
                ⟨layer, tree, kind, 0, UInt32.ofNat (h + 1), UInt32.ofNat nodeIdx⟩ [sub, sib] =
              thCall suite tagThH pkSeed
                ⟨layer, tree, kind, 0, UInt32.ofNat (h + 1), UInt32.ofNat nodeIdx⟩
                [computeMerkleNode suite pkSeed layer tree kind leafFn h (2 * nodeIdx),
                 computeMerkleNode suite pkSeed layer tree kind leafFn h (2 * nodeIdx + 1)] := by
            rw [computeMerkleNode_succ] at hW
            simp only [walkMerkleAuthPath, hHalf, ↓reduceIte, hSub, Option.some.injEq, thNodeH_eq] at hW
            exact hW
          match prodThCallSplit suite hCallEq with
          | .inl hArgs =>
            have hSubEq : walkMerkleAuthPath suite pkSeed layer tree kind h (2 * nodeIdx) localIdx
                leaf rest =
                some (computeMerkleNode suite pkSeed layer tree kind leafFn h (2 * nodeIdx)) := by
              simp only [List.cons.injEq, and_true] at hArgs
              rw [← hArgs.1]; exact hSub
            prodWalkMerkleExtract suite pkSeed layer tree kind leafFn U H C mkCol
              h (2 * nodeIdx) localIdx leaf rest (Nat.le_of_succ_le hLe) hHalf
              (by rw [← hMul]; exact hU) hSubEq
          | .inr ⟨hNe, hHash⟩ => .inr (mkCol h nodeIdx sub sib hLe hLo hHi hNe hHash)
      else
        match hSub : walkMerkleAuthPath suite pkSeed layer tree kind h (2 * nodeIdx + 1)
            (localIdx - 2 ^ h) leaf rest with
        | none =>
          False.elim (by simp only [walkMerkleAuthPath, hHalf, ↓reduceIte, hSub] at hW; cases hW)
        | some sub =>
          have hSubLt : localIdx - 2 ^ h < 2 ^ h := by rw [Nat.pow_succ] at hLt; omega
          have hIdxEq : nodeIdx * 2 ^ (h + 1) + localIdx =
              (2 * nodeIdx + 1) * 2 ^ h + (localIdx - 2 ^ h) := by
            rw [hMul, Nat.add_mul, Nat.one_mul, Nat.add_assoc,
              Nat.add_sub_of_le (Nat.le_of_not_lt hHalf)]
          have hCallEq :
              thCall suite tagThH pkSeed
                ⟨layer, tree, kind, 0, UInt32.ofNat (h + 1), UInt32.ofNat nodeIdx⟩ [sib, sub] =
              thCall suite tagThH pkSeed
                ⟨layer, tree, kind, 0, UInt32.ofNat (h + 1), UInt32.ofNat nodeIdx⟩
                [computeMerkleNode suite pkSeed layer tree kind leafFn h (2 * nodeIdx),
                 computeMerkleNode suite pkSeed layer tree kind leafFn h (2 * nodeIdx + 1)] := by
            rw [computeMerkleNode_succ] at hW
            simp only [walkMerkleAuthPath, hHalf, ↓reduceIte, hSub, Option.some.injEq, thNodeH_eq] at hW
            exact hW
          match prodThCallSplit suite hCallEq with
          | .inl hArgs =>
            have hSubEq : walkMerkleAuthPath suite pkSeed layer tree kind h (2 * nodeIdx + 1)
                (localIdx - 2 ^ h) leaf rest =
                some (computeMerkleNode suite pkSeed layer tree kind leafFn h (2 * nodeIdx + 1)) := by
              simp only [List.cons.injEq, and_true] at hArgs
              rw [← hArgs.2]; exact hSub
            prodWalkMerkleExtract suite pkSeed layer tree kind leafFn U H C mkCol
              h (2 * nodeIdx + 1) (localIdx - 2 ^ h) leaf rest (Nat.le_of_succ_le hLe) hSubLt
              (by rw [← hIdxEq]; exact hU) hSubEq
          | .inr ⟨hNe, hHash⟩ => .inr (mkCol h nodeIdx sib sub hLe hLo hHi hNe hHash)

/-- `walkMerkleKp_meets_honest` returning the collision. The walk starts at height `H` with
    address index `root`; a node at depth `d` below the start with local index `b` has address
    index `root * 2 ^ d + b`. -/
@[expose] def prodWalkMerkleKpExtract (suite : TweakableHashSuite) (pkSeed : List UInt8)
    (layer : UInt32) (tree : UInt64) (kind : AdrsKind) (kp : UInt32)
    (leafFn : Nat → List UInt8) (root U H : Nat) (C : Type)
    (mkCol : ∀ (h d b : Nat) (x y : List UInt8),
      d + (h + 1) = H → b * 2 ^ (h + 1) ≤ U → U < (b + 1) * 2 ^ (h + 1) →
      thPreimage tagThH pkSeed
          ⟨layer, tree, kind, kp, UInt32.ofNat (h + 1), UInt32.ofNat (root * 2 ^ d + b)⟩ [x, y] ≠
        thPreimage tagThH pkSeed
          ⟨layer, tree, kind, kp, UInt32.ofNat (h + 1), UInt32.ofNat (root * 2 ^ d + b)⟩
          [computeMerkleNodeKp suite pkSeed layer tree kind kp leafFn h
             (2 * (root * 2 ^ d + b)) (2 * b),
           computeMerkleNodeKp suite pkSeed layer tree kind kp leafFn h
             (2 * (root * 2 ^ d + b) + 1) (2 * b + 1)] →
      suite.rawHash
          (thPreimage tagThH pkSeed
            ⟨layer, tree, kind, kp, UInt32.ofNat (h + 1), UInt32.ofNat (root * 2 ^ d + b)⟩ [x, y]) =
        suite.rawHash
          (thPreimage tagThH pkSeed
            ⟨layer, tree, kind, kp, UInt32.ofNat (h + 1), UInt32.ofNat (root * 2 ^ d + b)⟩
            [computeMerkleNodeKp suite pkSeed layer tree kind kp leafFn h
               (2 * (root * 2 ^ d + b)) (2 * b),
             computeMerkleNodeKp suite pkSeed layer tree kind kp leafFn h
               (2 * (root * 2 ^ d + b) + 1) (2 * b + 1)]) → C) :
    ∀ (h d localBase localIdx : Nat) (leaf : List UInt8) (path : List (List UInt8)),
      d + h = H → localIdx < 2 ^ h → localBase * 2 ^ h + localIdx = U →
      walkMerkleAuthPathKp suite pkSeed layer tree kind kp h (root * 2 ^ d + localBase) localIdx
          leaf path =
        some (computeMerkleNodeKp suite pkSeed layer tree kind kp leafFn h
          (root * 2 ^ d + localBase) localBase) →
      PSum (leaf = leafFn U) C
  | 0, d, localBase, localIdx, leaf, path, _, hLt, hU, hW =>
    match path, hW with
    | [], hW => .inl (by
        simp only [walkMerkleAuthPathKp, computeMerkleNodeKp_zero, Option.some.injEq] at hW
        have h0 : localIdx = 0 := by rw [Nat.pow_zero] at hLt; omega
        rw [h0, Nat.pow_zero, Nat.mul_one, Nat.add_zero] at hU
        rw [← hU]; exact hW)
    | _ :: _, hW => False.elim (by simp [walkMerkleAuthPathKp] at hW)
  | h + 1, d, localBase, localIdx, leaf, path, hD, hLt, hU, hW =>
    match path, hW with
    | [], hW => False.elim (by simp [walkMerkleAuthPathKp] at hW)
    | sib :: rest, hW =>
      have hMul : localBase * 2 ^ (h + 1) = (2 * localBase) * 2 ^ h := by
        rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm (localBase * 2 ^ h) 2, Nat.mul_assoc]
      have hLo : localBase * 2 ^ (h + 1) ≤ U := by rw [← hU]; exact Nat.le_add_right _ _
      have hHi : U < (localBase + 1) * 2 ^ (h + 1) := by
        rw [← hU, Nat.add_mul, Nat.one_mul]; exact Nat.add_lt_add_left hLt _
      have hPow : root * 2 ^ (d + 1) = 2 * (root * 2 ^ d) := by
        rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm]
      have hL : 2 * (root * 2 ^ d + localBase) = root * 2 ^ (d + 1) + 2 * localBase := by
        rw [hPow, Nat.mul_add]
      have hR : 2 * (root * 2 ^ d + localBase) + 1 = root * 2 ^ (d + 1) + (2 * localBase + 1) := by
        rw [hPow, Nat.mul_add, Nat.add_assoc]
      have hD' : d + 1 + h = H := by rw [Nat.add_assoc, Nat.add_comm 1 h]; exact hD
      if hHalf : localIdx < 2 ^ h then
        match hSub : walkMerkleAuthPathKp suite pkSeed layer tree kind kp h
            (2 * (root * 2 ^ d + localBase)) localIdx leaf rest with
        | none =>
          False.elim (by simp only [walkMerkleAuthPathKp, hHalf, ↓reduceIte, hSub] at hW; cases hW)
        | some sub =>
          have hCallEq :
              thCall suite tagThH pkSeed
                ⟨layer, tree, kind, kp, UInt32.ofNat (h + 1),
                  UInt32.ofNat (root * 2 ^ d + localBase)⟩ [sub, sib] =
              thCall suite tagThH pkSeed
                ⟨layer, tree, kind, kp, UInt32.ofNat (h + 1),
                  UInt32.ofNat (root * 2 ^ d + localBase)⟩
                [computeMerkleNodeKp suite pkSeed layer tree kind kp leafFn h
                   (2 * (root * 2 ^ d + localBase)) (2 * localBase),
                 computeMerkleNodeKp suite pkSeed layer tree kind kp leafFn h
                   (2 * (root * 2 ^ d + localBase) + 1) (2 * localBase + 1)] := by
            simp only [walkMerkleAuthPathKp, computeMerkleNodeKp_succ, hHalf, ↓reduceIte, hSub, thNodeH_eq,
              Option.some.injEq] at hW
            exact hW
          match prodThCallSplit suite hCallEq with
          | .inl hArgs =>
            have hSubEq : walkMerkleAuthPathKp suite pkSeed layer tree kind kp h
                (root * 2 ^ (d + 1) + 2 * localBase) localIdx leaf rest =
                some (computeMerkleNodeKp suite pkSeed layer tree kind kp leafFn h
                  (root * 2 ^ (d + 1) + 2 * localBase) (2 * localBase)) := by
              simp only [List.cons.injEq, and_true] at hArgs
              rw [← hL, ← hArgs.1]; exact hSub
            prodWalkMerkleKpExtract suite pkSeed layer tree kind kp leafFn root U H C mkCol
              h (d + 1) (2 * localBase) localIdx leaf rest hD' hHalf
              (by rw [← hMul]; exact hU) hSubEq
          | .inr ⟨hNe, hHash⟩ => .inr (mkCol h d localBase sub sib hD hLo hHi hNe hHash)
      else
        match hSub : walkMerkleAuthPathKp suite pkSeed layer tree kind kp h
            (2 * (root * 2 ^ d + localBase) + 1) (localIdx - 2 ^ h) leaf rest with
        | none =>
          False.elim (by simp only [walkMerkleAuthPathKp, hHalf, ↓reduceIte, hSub] at hW; cases hW)
        | some sub =>
          have hSubLt : localIdx - 2 ^ h < 2 ^ h := by rw [Nat.pow_succ] at hLt; omega
          have hIdxEq : localBase * 2 ^ (h + 1) + localIdx =
              (2 * localBase + 1) * 2 ^ h + (localIdx - 2 ^ h) := by
            rw [hMul, Nat.add_mul, Nat.one_mul, Nat.add_assoc,
              Nat.add_sub_of_le (Nat.le_of_not_lt hHalf)]
          have hCallEq :
              thCall suite tagThH pkSeed
                ⟨layer, tree, kind, kp, UInt32.ofNat (h + 1),
                  UInt32.ofNat (root * 2 ^ d + localBase)⟩ [sib, sub] =
              thCall suite tagThH pkSeed
                ⟨layer, tree, kind, kp, UInt32.ofNat (h + 1),
                  UInt32.ofNat (root * 2 ^ d + localBase)⟩
                [computeMerkleNodeKp suite pkSeed layer tree kind kp leafFn h
                   (2 * (root * 2 ^ d + localBase)) (2 * localBase),
                 computeMerkleNodeKp suite pkSeed layer tree kind kp leafFn h
                   (2 * (root * 2 ^ d + localBase) + 1) (2 * localBase + 1)] := by
            simp only [walkMerkleAuthPathKp, computeMerkleNodeKp_succ, hHalf, ↓reduceIte, hSub, thNodeH_eq,
              Option.some.injEq] at hW
            exact hW
          match prodThCallSplit suite hCallEq with
          | .inl hArgs =>
            have hSubEq : walkMerkleAuthPathKp suite pkSeed layer tree kind kp h
                (root * 2 ^ (d + 1) + (2 * localBase + 1)) (localIdx - 2 ^ h) leaf rest =
                some (computeMerkleNodeKp suite pkSeed layer tree kind kp leafFn h
                  (root * 2 ^ (d + 1) + (2 * localBase + 1)) (2 * localBase + 1)) := by
              simp only [List.cons.injEq, and_true] at hArgs
              rw [← hR, ← hArgs.2]; exact hSub
            prodWalkMerkleKpExtract suite pkSeed layer tree kind kp leafFn root U H C mkCol
              h (d + 1) (2 * localBase + 1) (localIdx - 2 ^ h) leaf rest hD' hSubLt
              (by rw [← hIdxEq]; exact hU) hSubEq
          | .inr ⟨hNe, hHash⟩ => .inr (mkCol h d localBase sib sub hD hLo hHi hNe hHash)

/-- `wotsChain_meets_honest_gen` returning the collision. `top` is the step the chain ends at;
    every returned step satisfies `s + 1 ≤ top`. -/
@[expose] def prodChainExtract (suite : TweakableHashSuite) (sk : PqSecretKey)
    (layer : UInt32) (tree : UInt64) (kp r top : Nat) (C : Type)
    (mkCol : ∀ (s : Nat) (x : List UInt8), s + 1 ≤ top →
      thPreimage tagThF sk.pkSeed
          ⟨layer, tree, .wotsHash, UInt32.ofNat kp, UInt32.ofNat r, UInt32.ofNat s⟩ [x] ≠
        thPreimage tagThF sk.pkSeed
          ⟨layer, tree, .wotsHash, UInt32.ofNat kp, UInt32.ofNat r, UInt32.ofNat s⟩
          [honestChainNode suite sk layer tree kp r s] →
      suite.rawHash
          (thPreimage tagThF sk.pkSeed
            ⟨layer, tree, .wotsHash, UInt32.ofNat kp, UInt32.ofNat r, UInt32.ofNat s⟩ [x]) =
        suite.rawHash
          (thPreimage tagThF sk.pkSeed
            ⟨layer, tree, .wotsHash, UInt32.ofNat kp, UInt32.ofNat r, UInt32.ofNat s⟩
            [honestChainNode suite sk layer tree kp r s]) → C) :
    ∀ (k s : Nat) (x : List UInt8), s + k = top →
      wotsChainSteps suite sk.pkSeed layer tree kp r s k x =
        honestChainNode suite sk layer tree kp r (s + k) →
      PSum (x = honestChainNode suite sk layer tree kp r s) C
  | 0, s, x, _, h => .inl (by rw [wotsChainSteps_zero, Nat.add_zero] at h; exact h)
  | k + 1, s, x, hTop, h =>
    have hNext : wotsChainSteps suite sk.pkSeed layer tree kp r (s + 1) k
        (thChainF suite sk.pkSeed
          ⟨layer, tree, .wotsHash, UInt32.ofNat kp, UInt32.ofNat r, UInt32.ofNat s⟩ x) =
        honestChainNode suite sk layer tree kp r ((s + 1) + k) := by
      rw [wotsChainSteps_succ] at h
      dsimp only at h
      rw [show s + (k + 1) = (s + 1) + k by omega] at h
      exact h
    match prodChainExtract suite sk layer tree kp r top C mkCol k (s + 1) _ (by omega) hNext with
    | .inr c => .inr c
    | .inl hF =>
      have hCallEq :
          thCall suite tagThF sk.pkSeed
            ⟨layer, tree, .wotsHash, UInt32.ofNat kp, UInt32.ofNat r, UInt32.ofNat s⟩ [x] =
          thCall suite tagThF sk.pkSeed
            ⟨layer, tree, .wotsHash, UInt32.ofNat kp, UInt32.ofNat r, UInt32.ofNat s⟩
            [honestChainNode suite sk layer tree kp r s] := by
        rw [← thChainF_eq, ← thChainF_eq, honestChainNode_succ]
        exact hF
      match prodThCallSplit suite hCallEq with
      | .inl hArgs => .inl (List.cons.inj hArgs).1
      | .inr ⟨hNe, hHash⟩ => .inr (mkCol s x (by omega) hNe hHash)

/-- All chains of one WOTS signature whose recovered endpoints are the honest endpoints: each
    chain value is the honest node at its digit, or a chain step collides. -/
@[expose] def prodAllChainsExtract (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (layer : UInt32) (tree : UInt64) (kp : Nat)
    (digF : List Nat) (chains : List (List UInt8)) (C : Type)
    (mkCol : ∀ (r s : Nat) (x : List UInt8), r < params.ell1 → s + 1 ≤ params.w - 1 →
      thPreimage tagThF sk.pkSeed
          ⟨layer, tree, .wotsHash, UInt32.ofNat kp, UInt32.ofNat r, UInt32.ofNat s⟩ [x] ≠
        thPreimage tagThF sk.pkSeed
          ⟨layer, tree, .wotsHash, UInt32.ofNat kp, UInt32.ofNat r, UInt32.ofNat s⟩
          [honestChainNode suite sk layer tree kp r s] →
      suite.rawHash
          (thPreimage tagThF sk.pkSeed
            ⟨layer, tree, .wotsHash, UInt32.ofNat kp, UInt32.ofNat r, UInt32.ofNat s⟩ [x]) =
        suite.rawHash
          (thPreimage tagThF sk.pkSeed
            ⟨layer, tree, .wotsHash, UInt32.ofNat kp, UInt32.ofNat r, UInt32.ofNat s⟩
            [honestChainNode suite sk layer tree kp r s]) → C)
    (hEnds : recoverWotsEndpoints suite params sk.pkSeed layer tree kp digF chains =
      (List.range params.ell1).map fun r => honestChainNode suite sk layer tree kp r (params.w - 1))
    (hTsw : checkTargetSum params.w params.ell1 params.targetSum digF = true) :
    ∀ (m : Nat), m ≤ params.ell1 →
      PSum (∀ r, r < m → chains.getD r [] = honestChainNode suite sk layer tree kp r (digF.getD r 0)) C
  | 0, _ => .inl (fun _ hLt => absurd hLt (Nat.not_lt_zero _))
  | m + 1, hmLe =>
    match prodAllChainsExtract suite params sk layer tree kp digF chains C mkCol hEnds hTsw m
        (Nat.le_of_succ_le hmLe) with
    | .inr col => .inr col
    | .inl hPrev =>
      have hmLt : m < params.ell1 := hmLe
      have hSum : digF.getD m 0 + (params.w - 1 - digF.getD m 0) = params.w - 1 := by
        obtain ⟨hLenF, hBoundF, _⟩ := (checkTargetSum_iff _ _ _ _).mp hTsw
        have hmLen : m < digF.length := by rw [hLenF]; exact hmLt
        have hdLt : digF.getD m 0 < params.w := by
          rw [list_getD_eq_getElem digF 0 hmLen]
          exact hBoundF _ (List.getElem_mem hmLen)
        omega
      have hStepEq :
          wotsChainSteps suite sk.pkSeed layer tree kp m (digF.getD m 0)
            (params.w - 1 - digF.getD m 0) (chains.getD m []) =
          honestChainNode suite sk layer tree kp m
            (digF.getD m 0 + (params.w - 1 - digF.getD m 0)) := by
        have hAt := congrArg (fun l => l.getD m []) hEnds
        rw [recoverWotsEndpoints_eq, list_getD_map_range params.ell1 _ [] hmLt,
            list_getD_map_range params.ell1 _ [] hmLt] at hAt
        rw [hSum]
        exact hAt
      match prodChainExtract suite sk layer tree kp m (params.w - 1) C
          (fun s x hs hNe hHash => mkCol m s x hmLt hs hNe hHash)
          (params.w - 1 - digF.getD m 0) (digF.getD m 0) (chains.getD m []) hSum hStepEq with
      | .inr col => .inr col
      | .inl hM =>
        .inl (fun r hr => by
          rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hr) with hlt | rfl
          · exact hPrev r hlt
          · exact hM)

end Qsag
end

#verify_constructive Qsag.ProdTargetIdx.input_honest Qsag.ProdTcrWitness.toSmTcrBreak
#verify_constructive Qsag.ProdTcrWitness.check

/-!
# Qsag.Protocol.Signing.ProdCollisionLayers — hypertree part of the production extractor

`prodLayerExtract` and `prodHypertreeWalkExtract` are `prod_layer_divergence_break` and
`prod_hypertree_walk_break` as functions. Every case split is on decidable data (log search,
codeword equality, preimage equality), so the returned `ProdTcrWitness` is the collision the
verifier walk meets. The preimage event stays a proposition; its two cases are
`prod_layer_preimage_logged` and `prod_layer_preimage_unused`.

Scope. Deterministic extraction only; see `ProdCollisionWitness`.
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
-- Codeword digits the verifier derives for layer message `cur` at layer `i`.
set_option hygiene false in
local notation:max "digs⟪" i "⟫" =>
  (extractBaseWDigits params.w params.ell1
    (productionLayerDigest suite params sigStar.rRand sk.pkSeed
      (derivePublicKey suite params sk).pkRoot cur i
      (UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) /
        2 ^ params.subtreeHeight))
      (UInt32.ofNat (sigStar.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) %
        2 ^ params.subtreeHeight))
      (sigStar.layerSigs.getD i ⟨0, [], []⟩).tswCtr))
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

/-! ### Propositional parts of the traversal -/

theorem prod_list_range_succ_shift {α : Type} (rem : Nat) (f : Nat → α) :
    (List.range (rem + 1)).map f = f 0 :: (List.range rem).map (fun k => f (k + 1)) := by
  induction rem generalizing f with
  | zero => simp
  | succ r ih => rw [List.range_succ, List.map_append, ih f, List.range_succ, List.map_append]; simp

theorem prod_sumDigits_ge_mul (bound : Nat) :
    ∀ (ds : List Nat), (∀ d ∈ ds, bound ≤ d) → bound * ds.length ≤ sumDigits ds
  | [], _ => by simp [sumDigits_nil]
  | d :: ds, hAll => by
    rw [sumDigits_cons, List.length_cons, Nat.mul_succ]
    have hd : bound ≤ d := hAll d (.head ds)
    have hRest := prod_sumDigits_ge_mul bound ds (fun x hx => hAll x (.tail d hx))
    omega

theorem prod_findDigitLt_none (maxVal : Nat) :
    ∀ (ds : List Nat), findDigitLt maxVal ds = none → ∀ d ∈ ds, maxVal ≤ d :=
  findDigitLt_none_all_ge maxVal

/-- Honest chain values under a codeword different from the logged one at the same position
    contain a preimage below the logged digit. -/
theorem prod_layer_preimage_logged (suite : TweakableHashSuite) (params : PqHashParams) (sk :
    PqSecretKey)
    (log : List (List UInt8 × PqHashSig)) (msgStar : List UInt8) (sigStar : PqHashSig)
    (hCons : ProdLogConsistent suite params sk log)
    (i : Nat) (hi : i < params.numLayers) (digF : List Nat)
    (hTsw : checkTargetSum params.w params.ell1 params.targetSum digF = true)
    (hChains : ∀ r, r < params.ell1 →
      lsig⟪i⟫.wotsChains.getD r [] =
        honestChainNode suite sk (UInt32.ofNat i) tree⟪i⟫ kp⟪i⟫ r (digF.getD r 0))
    (e : List UInt8 × PqHashSig) (he : e ∈ log) (hOk : ProdLogEntryOk suite params sk e)
    (hPos : e.2.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) = pos⟪i⟫)
    (hDigNe : digF ≠ prodLogLayerDigits suite params sk e i) :
    ProdPreimageBreak suite params sk log msgStar sigStar := by
  have hValidH := prodLogLayerDigits_valid hOk i hi
  obtain ⟨hLenF, _, _⟩ := (checkTargetSum_iff _ _ _ _).mp hTsw
  obtain ⟨r, hr2, hr1, hlt, hbw⟩ :=
    (tsw_incomparable_no_chain_forgery hValidH hTsw (fun hEq => hDigNe hEq.symm)).2
  have hr : r < params.ell1 := by rw [← hLenF]; exact hr2
  have hF : digF.getD r 0 = digF[r] := list_getD_eq_getElem digF 0 hr2
  have hH : (prodLogLayerDigits suite params sk e i).getD r 0 =
      (prodLogLayerDigits suite params sk e i)[r] := list_getD_eq_getElem _ 0 hr1
  refine ProdPreimageBreak.wots i hi r hr (digF.getD r 0) (by omega) ?_ ?_
  · rw [hChains r hr]
    exact honestChainNode_succ suite sk (UInt32.ofNat i) _ _ r (digF.getD r 0)
  · intro e' he' hPos'
    rw [hCons e' he' e he i hi (hPos'.trans hPos.symm)]
    omega

/-- Honest chain values at a position no logged signature used contain a preimage. -/
theorem prod_layer_preimage_unused (suite : TweakableHashSuite) (params : PqHashParams) (sk :
    PqSecretKey)
    (log : List (List UInt8 × PqHashSig)) (msgStar : List UInt8) (sigStar : PqHashSig)
    (hw : params.w = 4 ∨ params.w = 16) (hPwf : params.productionWellFormed = true)
    (i : Nat) (hi : i < params.numLayers) (digF : List Nat)
    (hTsw : checkTargetSum params.w params.ell1 params.targetSum digF = true)
    (hChains : ∀ r, r < params.ell1 →
      lsig⟪i⟫.wotsChains.getD r [] =
        honestChainNode suite sk (UInt32.ofNat i) tree⟪i⟫ kp⟪i⟫ r (digF.getD r 0))
    (hNoUse : ∀ e, e ∈ log → ¬ e.2.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) = pos⟪i⟫) :
    ProdPreimageBreak suite params sk log msgStar sigStar := by
  have hGeom := params.productionWellFormed_geom hPwf hw
  have hStrict : params.targetSum < (params.w - 1) * params.ell1 := by
    rw [PqHashParams.targetSum_eq]
    rcases hGeom with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> decide
  obtain ⟨hLenF, hBoundF, hSumF⟩ := (checkTargetSum_iff _ _ _ _).mp hTsw
  cases hFind : findDigitLt (params.w - 1) digF with
  | none =>
    exfalso
    have hAllGe := prod_findDigitLt_none (params.w - 1) digF hFind
    have hGe := prod_sumDigits_ge_mul (params.w - 1) digF hAllGe
    rw [hLenF, hSumF] at hGe
    omega
  | some r =>
    obtain ⟨hrLen, hrVal⟩ := findDigitLt_sound (params.w - 1) hFind
    have hr : r < params.ell1 := by rw [← hLenF]; exact hrLen
    have hF : digF.getD r 0 = digF[r] := list_getD_eq_getElem digF 0 hrLen
    refine ProdPreimageBreak.wots i hi r hr (digF.getD r 0) (by omega) ?_ ?_
    · rw [hChains r hr]
      exact honestChainNode_succ suite sk (UInt32.ofNat i) _ _ r (digF.getD r 0)
    · intro e' he' hPos'
      exact absurd hPos' (hNoUse e' he')

theorem prod_recoverForsTreeRoots_succ_inv (suite : TweakableHashSuite) (params : PqHashParams)
    (pkSeed : List UInt8) (treeIdx : UInt64) (kpIdx : Nat)
    (idxs : List Nat) (openings : List ForsTreeOpening) (j rem : Nat) (roots : List (List UInt8))
    (h : recoverProductionForsTreeRoots suite params pkSeed treeIdx kpIdx idxs openings j (rem + 1)
        =
      some roots) :
    ∃ rJ rs,
      walkMerkleAuthPathKp suite pkSeed 0 treeIdx .forsTree (UInt32.ofNat kpIdx)
        params.forsHeight j (idxs.getD j 0)
        (forsIndexedLeafHash suite pkSeed treeIdx kpIdx j (idxs.getD j 0)
          (openings.getD j ⟨[], []⟩).secretVal)
        (openings.getD j ⟨[], []⟩).authPath = some rJ ∧
      recoverProductionForsTreeRoots suite params pkSeed treeIdx kpIdx idxs openings (j + 1) rem =
        some rs ∧
      roots = rJ :: rs := by
  rw [recoverProductionForsTreeRoots_succ] at h
  dsimp only at h
  split at h
  · cases h
  · rename_i rJ hWalk
    split at h
    · cases h
    · rename_i rs hRest
      simp only [Option.some.injEq] at h
      exact ⟨rJ, rs, hWalk, hRest, h.symm⟩

theorem prod_recoverForsPk_some_inv (suite : TweakableHashSuite) (params : PqHashParams)
    (pkSeed : List UInt8) (treeIdx : UInt64) (kpIdx : Nat)
    (idxs : List Nat) (openings : List ForsTreeOpening) (pk : List UInt8)
    (h : recoverProductionForsPk suite params pkSeed treeIdx kpIdx idxs openings = some pk) :
    ∃ roots,
      recoverProductionForsTreeRoots suite params pkSeed treeIdx kpIdx idxs openings 0
        params.forsTrees = some roots ∧
      pk = thTweakTl suite pkSeed ⟨0, treeIdx, .forsRoots, UInt32.ofNat kpIdx, 0, 0⟩ roots := by
  rw [recoverProductionForsPk_eq] at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i roots hRoots
      simp only [Option.some.injEq] at h
      exact ⟨roots, hRoots, h.symm⟩

/-- What acceptance of a stateless production signature fixes, with the FORS indices named by
    `prodSigForsIdxs` instead of an existential. -/
theorem prod_stateless_accept_facts (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (msgStar : List UInt8) (sigStar : PqHashSig)
    (hStateless : params.statefulJorts = false)
    (hAccept : verifyProductionPqHashSig suite params (derivePublicKey suite params sk) msgStar
      sigStar = true) :
    params.productionWellFormed = true ∧ sigStar.layerSigs.length = params.numLayers ∧
    sigStar.leafGlobalIdx < 2 ^ (params.numLayers * params.subtreeHeight) ∧
    (FORS_IDXS).length = params.forsTrees ∧
    (∀ idx ∈ (FORS_IDXS), idx < 2 ^ params.forsHeight) ∧
    ∃ forsPkF,
      recoverProductionForsPk suite params sk.pkSeed FORS_TREE FORS_KP (FORS_IDXS)
          sigStar.forsOpenings =
        some forsPkF ∧
      verifyProductionHypertreeLayers suite params sk.pkSeed PK_ROOT sigStar.rRand 0
        sigStar.leafGlobalIdx forsPkF sigStar.layerSigs = some PK_ROOT := by
  obtain ⟨hPwf, hLen, _, idxs, forsPkF, hD, hFors, hHt⟩ :=
    verifyProductionPqHashSig_stateless_inv suite params _ msgStar sigStar hStateless hAccept
  obtain ⟨_, _, hLt, hILen, hIBnd⟩ := deriveProductionStatelessInputs_bounds _ _ _ _ _ _ _ _ hD
  have hI : (FORS_IDXS) = idxs := by
    unfold prodSigForsIdxs
    rw [hD]
  rw [hI]
  exact ⟨hPwf, hLen, hLt, hILen, hIBnd, forsPkF, hFors, hHt⟩

/-- Every accepted production signature names a leaf of the hypertree. -/
theorem production_accept_leaf_lt (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (msgStar : List UInt8) (sigStar : PqHashSig)
    (hAccept : verifyProductionPqHashSig suite params (derivePublicKey suite params sk) msgStar
      sigStar = true) :
    sigStar.leafGlobalIdx < 2 ^ (params.numLayers * params.subtreeHeight) := by
  cases hSt : params.statefulJorts
  · exact (prod_stateless_accept_facts suite params sk msgStar sigStar hSt hAccept).2.2.1
  · exact (verifyProductionPqHashSig_stateful_inv suite params _ msgStar sigStar hSt hAccept).2.2.1

/-! ### One hypertree layer -/

/-- `prod_layer_divergence_break` as a function: the collision met on the XMSS path, the WOTS
    public-key compression, a chain step or the layer digest, or else the preimage event. -/
@[expose] def prodLayerExtract (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey)
    (log : List (List UInt8 × PqHashSig)) (msgStar : List UInt8) (sigStar : PqHashSig)
    (hw : params.w = 4 ∨ params.w = 16) (hPwf : params.productionWellFormed = true)
    (hLog : ∀ e ∈ log, ProdLogEntryOk suite params sk e)
    (hCons : ProdLogConsistent suite params sk log)
    (i : Nat) (hi : i < params.numLayers) (cur : List UInt8) (digF : List Nat)
    (hDigF : digF = digs⟪i⟫)
    (hDiff : ∀ e ∈ log, e.2.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) = pos⟪i⟫ →
      cur ≠ prodHonestLayerMsg suite params sk e i)
    (hTsw : checkTargetSum params.w params.ell1 params.targetSum digF = true)
    (hWalk : walkMerkleAuthPath suite sk.pkSeed (UInt32.ofNat i) tree⟪i⟫ .tree params.subtreeHeight
        0
        kp⟪i⟫
        (recoverWotsPkFromSig suite params sk.pkSeed (UInt32.ofNat i) tree⟪i⟫ kp⟪i⟫ digF
          lsig⟪i⟫.wotsChains)
        lsig⟪i⟫.authPath =
      some (computeXmssSubtreeRoot suite params sk (UInt32.ofNat i) tree⟪i⟫)) :
    PSum (ProdTcrWitness suite params sk log msgStar sigStar) (ProdPreimageBreak suite params sk
        log msgStar sigStar) :=
  have hKpLt : kp⟪i⟫ < 2 ^ params.subtreeHeight := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hWalkNode : walkMerkleAuthPath suite sk.pkSeed (UInt32.ofNat i) tree⟪i⟫ .tree
      params.subtreeHeight 0 kp⟪i⟫
      (recoverWotsPkFromSig suite params sk.pkSeed (UInt32.ofNat i) tree⟪i⟫ kp⟪i⟫ digF
        lsig⟪i⟫.wotsChains)
      lsig⟪i⟫.authPath =
      some (computeMerkleNode suite sk.pkSeed (UInt32.ofNat i) tree⟪i⟫ .tree
        (computeWotsPk suite params sk (UInt32.ofNat i) tree⟪i⟫) params.subtreeHeight 0) := by
    rw [← computeXmssSubtreeRoot_eq]; exact hWalk
  match prodWalkMerkleExtract suite sk.pkSeed (UInt32.ofNat i) tree⟪i⟫ .tree
      (computeWotsPk suite params sk (UInt32.ofNat i) tree⟪i⟫) kp⟪i⟫ params.subtreeHeight
      (ProdTcrWitness suite params sk log msgStar sigStar)
      (fun h n a b hH hLo hHi hNe hHash =>
        ⟨.xmssNode i h n, _, ⟨hi, hH, hLo, hHi⟩, ⟨a, b, rfl⟩,
          (by rw [ProdTargetIdx.input_xmssNode]; exact hNe),
          (by rw [ProdTargetIdx.input_xmssNode]; exact hHash)⟩)
      params.subtreeHeight 0 kp⟪i⟫ _ _ (Nat.le_refl _) hKpLt
      (by rw [Nat.zero_mul, Nat.zero_add]) hWalkNode with
  | .inr w => .inl w
  | .inl hPk =>
    have hTlEq :
        thCall suite tagThTl sk.pkSeed ⟨UInt32.ofNat i, tree⟪i⟫, .wotsPk, UInt32.ofNat kp⟪i⟫, 0, 0⟩
          (recoverWotsEndpoints suite params sk.pkSeed (UInt32.ofNat i) tree⟪i⟫ kp⟪i⟫ digF
            lsig⟪i⟫.wotsChains) =
        thCall suite tagThTl sk.pkSeed ⟨UInt32.ofNat i, tree⟪i⟫, .wotsPk, UInt32.ofNat kp⟪i⟫, 0, 0⟩
          ((List.range params.ell1).map fun r =>
            honestChainNode suite sk (UInt32.ofNat i) tree⟪i⟫ kp⟪i⟫ r (params.w - 1)) := by
      rw [recoverWotsPkFromSig_eq, computeWotsPk_eq, thTweakTl_eq, thTweakTl_eq] at hPk
      exact hPk
    match prodThCallSplit suite hTlEq with
    | .inr ⟨hNe, hHash⟩ =>
      .inl ⟨.wotsPk i, _, hi,
        ⟨recoverWotsEndpoints suite params sk.pkSeed (UInt32.ofNat i) tree⟪i⟫ kp⟪i⟫ digF
          lsig⟪i⟫.wotsChains, rfl⟩,
        (by rw [ProdTargetIdx.input_wotsPk]; exact hNe),
        (by rw [ProdTargetIdx.input_wotsPk]; exact hHash)⟩
    | .inl hEnds =>
      match prodAllChainsExtract suite params sk (UInt32.ofNat i) tree⟪i⟫ kp⟪i⟫ digF
          lsig⟪i⟫.wotsChains (ProdTcrWitness suite params sk log msgStar sigStar)
          (fun r s x hr hs hNe hHash => ⟨.chainStep i r s, _, ⟨hi, hr, hs⟩, ⟨x, rfl⟩,
            (by rw [ProdTargetIdx.input_chainStep]; exact hNe),
            (by rw [ProdTargetIdx.input_chainStep]; exact hHash)⟩)
          hEnds hTsw params.ell1 (Nat.le_refl _) with
      | .inr w => .inl w
      | .inl hChains =>
        match prodListSearch
            (fun e : List UInt8 × PqHashSig =>
              e.2.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) = pos⟪i⟫)
            (fun e =>
              if h : e.2.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) = pos⟪i⟫ then .inl h
              else .inr h) log with
        | .inr hNoUse =>
          .inr (prod_layer_preimage_unused suite params sk log msgStar sigStar hw hPwf i hi digF
              hTsw hChains hNoUse)
        | .inl ⟨e, ⟨he, hPos⟩⟩ =>
          if hDigEq : digF = prodLogLayerDigits suite params sk e i then
            if hPre : prodLayerPreimage params sigStar.rRand sk.pkSeed PK_ROOT cur i tree⟪i⟫
                (UInt32.ofNat kp⟪i⟫) lsig⟪i⟫.tswCtr =
                ProdTargetIdx.input suite params sk sigStar.leafGlobalIdx (.signedDigest e i) then
              False.elim (by
                simp only [ProdTargetIdx.input] at hPre
                rw [hPos] at hPre
                exact hDiff e he hPos (prodLayerPreimage_cur_inj hPre))
            else
              .inl ⟨.signedDigest e i, _, ⟨he, hi, hPos⟩, ⟨cur, rfl⟩, hPre, by
                have hDE := hDigEq
                rw [hDigF] at hDE
                unfold prodLogLayerDigits at hDE
                have hD := production_digits_inj params hw hPwf
                  (productionLayerDigest_length _ _ _ _ _ _ _ _ _ _)
                  (by
                    unfold prodLogLayerDigest
                    exact productionLayerDigest_length _ _ _ _ _ _ _ _ _ _)
                  hDE
                unfold prodLogLayerDigest at hD
                rw [productionLayerDigest_rawHash, productionLayerDigest_rawHash] at hD
                exact hD⟩
          else
            .inr (prod_layer_preimage_logged suite params sk log msgStar sigStar hCons i hi digF
                hTsw hChains e he
              (hLog e he) hPos hDigEq)

/-! ### The hypertree walk -/

/-- Result of walking the layers from `i` upward with layer message `cur`. -/
inductive ProdWalkOutcome (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey)
    (log : List (List UInt8 × PqHashSig)) (msgStar : List UInt8) (sigStar : PqHashSig) (i : Nat)
        (cur : List UInt8) : Type where
  /-- `cur` is the message the logged signature `e` signed at this position. -/
  | honest (e : List UInt8 × PqHashSig) (he : e ∈ log)
      (hPos : e.2.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) = pos⟪i⟫)
      (hEq : cur = prodHonestLayerMsg suite params sk e i)
  | tcr (w : ProdTcrWitness suite params sk log msgStar sigStar)
  | pre (h : ProdPreimageBreak suite params sk log msgStar sigStar)

/-- `prod_hypertree_walk_break` as a function. -/
@[expose] def prodHypertreeWalkExtract (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey)
    (log : List (List UInt8 × PqHashSig)) (msgStar : List UInt8) (sigStar : PqHashSig)
    (hw : params.w = 4 ∨ params.w = 16) (hPwf : params.productionWellFormed = true)
    (hLog : ∀ e ∈ log, ProdLogEntryOk suite params sk e)
    (hCons : ProdLogConsistent suite params sk log) :
    ∀ (sigs : List LayerXmssSig) (i : Nat) (cur : List UInt8),
      sigs ≠ [] →
      (∀ j, sigs.getD j ⟨0, [], []⟩ = sigStar.layerSigs.getD (i + j) ⟨0, [], []⟩) →
      i + sigs.length = params.numLayers →
      verifyProductionHypertreeLayers suite params sk.pkSeed PK_ROOT sigStar.rRand i (pos⟪i⟫) cur
          sigs =
        some TOP_ROOT →
      ProdWalkOutcome suite params sk log msgStar sigStar i cur
  | [], _, _, hNe, _, _, _ => absurd rfl hNe
  | lsig :: rest, i, cur, _, hAlign, hLenEq, hVer =>
    have hi : i < params.numLayers := by
      rw [← hLenEq, List.length_cons]
      omega
    have hLs : lsig = lsig⟪i⟫ := by
      have h := hAlign 0
      rw [List.getD_cons_zero, Nat.add_zero] at h
      exact h
    have hStep : pos⟪i⟫ / 2 ^ params.subtreeHeight =
        sigStar.leafGlobalIdx / 2 ^ ((i + 1) * params.subtreeHeight) := by
      have h := div_pow_mul_pow_mul sigStar.leafGlobalIdx i 1 params.subtreeHeight
      rw [Nat.one_mul] at h
      exact h
    have hInv := verifyProductionHypertreeLayers_cons_inv suite params _ _ _ _ _ _ _ _ _ hVer
    have hTsw : checkTargetSum params.w params.ell1 params.targetSum digs⟪i⟫ = true := by
      rw [← hLs]; exact hInv.2.1
    match hNextW : walkMerkleAuthPath suite sk.pkSeed (UInt32.ofNat i) tree⟪i⟫ .tree
        params.subtreeHeight 0 kp⟪i⟫
        (recoverWotsPkFromSig suite params sk.pkSeed (UInt32.ofNat i) tree⟪i⟫ kp⟪i⟫ digs⟪i⟫
          lsig⟪i⟫.wotsChains)
        lsig⟪i⟫.authPath with
    | none => False.elim (by
        obtain ⟨_, _, n', hW, _⟩ := hInv
        rw [hLs] at hW
        rw [hNextW] at hW
        cases hW)
    | some next =>
      have hRest : verifyProductionHypertreeLayers suite params sk.pkSeed PK_ROOT sigStar.rRand (i
          + 1)
          (sigStar.leafGlobalIdx / 2 ^ ((i + 1) * params.subtreeHeight)) next rest = some TOP_ROOT
              := by
        obtain ⟨_, _, n', hW, hR⟩ := hInv
        rw [hLs] at hW
        rw [hNextW] at hW
        have hn : next = n' := Option.some.inj hW
        rw [← hn, hStep] at hR
        exact hR
      let step : PSum (next = computeXmssSubtreeRoot suite params sk (UInt32.ofNat i) tree⟪i⟫)
          (PSum (ProdTcrWitness suite params sk log msgStar sigStar) (ProdPreimageBreak suite
              params sk log msgStar sigStar)) :=
        match hR : rest with
        | [] => .inl (by
            have hRest' := hRest
            rw [hR, verifyProductionHypertreeLayers_nil] at hRest'
            simp only [Option.some.injEq] at hRest'
            have hD : params.numLayers = i + 1 := by
              rw [← hLenEq, hR, List.length_cons, List.length_nil]
            rw [hD, Nat.add_sub_cancel] at hRest'
            rw [hStep]
            exact hRest')
        | _ :: _ =>
          match prodHypertreeWalkExtract suite params sk log msgStar sigStar hw hPwf hLog hCons
              rest (i + 1) next
              (by rw [hR]; exact List.cons_ne_nil _ _)
              (fun j => by
                have h := hAlign (j + 1)
                rw [List.getD_cons_succ] at h
                rw [h, show i + (j + 1) = i + 1 + j by omega])
              (by rw [← hLenEq, List.length_cons]; omega)
              hRest with
          | .honest e _ hPos hEq => .inl (by
              rw [hEq]
              unfold prodHonestLayerMsg
              simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
              rw [hPos, hStep])
          | .tcr w => .inr (.inl w)
          | .pre h => .inr (.inr h)
      match step with
      | .inr (.inl w) => .tcr w
      | .inr (.inr h) => .pre h
      | .inl hNext =>
        match prodListSearch
            (fun e : List UInt8 × PqHashSig =>
              e.2.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) = pos⟪i⟫ ∧
              cur = prodHonestLayerMsg suite params sk e i)
            (fun e =>
              if h : e.2.leafGlobalIdx / 2 ^ (i * params.subtreeHeight) = pos⟪i⟫ ∧
                  cur = prodHonestLayerMsg suite params sk e i then .inl h
              else .inr h) log with
        | .inl ⟨e, ⟨he, hP⟩⟩ => .honest e he hP.1 hP.2
        | .inr hNone =>
          match prodLayerExtract suite params sk log msgStar sigStar hw hPwf hLog hCons i hi cur
              digs⟪i⟫ rfl
              (fun e he hPos hEq => hNone e he ⟨hPos, hEq⟩) hTsw
              (by rw [← hNext]; exact hNextW) with
          | .inl w => .tcr w
          | .inr h => .pre h

end Qsag
end

#verify_constructive Qsag.prod_layer_preimage_logged Qsag.prod_layer_preimage_unused
#verify_constructive Qsag.production_accept_leaf_lt

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
@[expose] def prodForsRootsExtract (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey)
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
@[expose] def prodForsExtract (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey)
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
    | .inr ⟨hNe, hHash⟩ =>
      .tcr ⟨.forsRoots, _, hStateless, ⟨rootsF, rfl⟩,
        (by rw [ProdTargetIdx.input_forsRoots]; exact hNe),
        (by rw [ProdTargetIdx.input_forsRoots]; exact hHash)⟩
    | .inl hArgs =>
      have hIdxs : ∀ J, J < params.forsTrees → (FORS_IDXS).getD J 0 < 2 ^ params.forsHeight := by
        intro J hJ
        have hJLen : J < (FORS_IDXS).length := by rw [hLenI]; exact hJ
        rw [list_getD_eq_getElem _ 0 hJLen]
        exact hBnd _ (List.getElem_mem hJLen)
      match prodForsRootsExtract suite params sk FORS_TREE FORS_KP (FORS_IDXS) sigStar.forsOpenings
          (ProdTcrWitness suite params sk log msgStar sigStar)
          (fun j h d b x y hj hD hLo hHi hNe hHash =>
            ⟨.forsNode j h d b, _, ⟨hStateless, hj, hD, hLo, hHi⟩, ⟨x, y, rfl⟩,
              (by rw [ProdTargetIdx.input_forsNode]; exact hNe),
              (by rw [ProdTargetIdx.input_forsNode]; exact hHash)⟩)
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
@[expose] def production_stateful_forgery_extract (suite : TweakableHashSuite) (params : PqHashParams)
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
    | .inr ⟨hNe', hHash⟩ =>
      .inl ⟨.preHash e, _, ⟨he, hStateful⟩, rfl,
        (by rw [ProdTargetIdx.input_preHash]; exact hNe'),
        (by rw [ProdTargetIdx.input_preHash]; exact hHash)⟩

/-- **Stateless production profiles.** -/
@[expose] def production_stateless_forgery_extract (suite : TweakableHashSuite) (params : PqHashParams)
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

theorem production_forgery_extract_false (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (queries : List ProdSigningQuery) (msgStar : List UInt8) (sigStar : PqHashSig)
    (hw : params.w = 4 ∨ params.w = 16) (hSt : params.statefulJorts = false)
    (hOneTime : params.statefulJorts = true →
      ∀ q, q ∈ queries → ∀ q', q' ∈ queries → q.epoch = q'.epoch → q = q')
    (hFresh : ∀ e ∈ productionSigningLog suite params sk queries, e.1 ≠ msgStar)
    (hAccept : verifyProductionPqHashSig suite params (derivePublicKey suite params sk) msgStar sigStar = true) :
    production_forgery_extract suite params sk queries msgStar sigStar hw hOneTime hFresh hAccept =
      production_stateless_forgery_extract suite params sk queries msgStar sigStar hw hSt hFresh hAccept := by
  unfold production_forgery_extract
  split
  · rfl
  · rename_i hTrue; rw [hSt] at hTrue; cases hTrue

theorem production_forgery_extract_true (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (queries : List ProdSigningQuery) (msgStar : List UInt8) (sigStar : PqHashSig)
    (hw : params.w = 4 ∨ params.w = 16) (hSt : params.statefulJorts = true)
    (hOneTime : params.statefulJorts = true →
      ∀ q, q ∈ queries → ∀ q', q' ∈ queries → q.epoch = q'.epoch → q = q')
    (hFresh : ∀ e ∈ productionSigningLog suite params sk queries, e.1 ≠ msgStar)
    (hAccept : verifyProductionPqHashSig suite params (derivePublicKey suite params sk) msgStar sigStar = true) :
    production_forgery_extract suite params sk queries msgStar sigStar hw hOneTime hFresh hAccept =
      (match production_stateful_forgery_extract suite params sk queries msgStar sigStar hw hSt
          (hOneTime hSt) hFresh hAccept with
       | .inl w => .tcr w
       | .inr h => .pre h) := by
  unfold production_forgery_extract
  split
  · rename_i hFalse; rw [hSt] at hFalse; cases hFalse
  · rfl


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

end Qsag
end

#verify_constructive Qsag.ProdBreakWitness.toBreak
#verify_constructive Qsag.production_stateful_forgery_witness Qsag.production_forgery_witness
#verify_constructive Qsag.validProductionJortsBatch_item_forgery_witness
#verify_constructive Qsag.production_forgery_break_via_extract
#verify_constructive Qsag.production_checked_stateless_forgery_witness

/-!
# Qsag.Protocol.Signing.ProdCollisionEvents — winning events defined from the extractor output

`prodOutcomeBreak` runs `production_forgery_extract` on a game outcome. `prodTcrOutput` is the
`(target, colliding input)` pair it returns, and `prodTcrEvent` is the executable check
`prodTcrCheck` on that pair. `production_euf_cma_extracted_bound` counts wins against the three
events defined this way. It has no supplied event and no hypothesis covering `ProdSmTcrBreak`,
which is what `production_euf_cma_advantage_bound` requires of its caller.

Scope. The count is a deterministic classification over a finite coin list. It assigns no
probability to the three events and does not model the hash as an oracle, so it is not yet a
bound by a primitive advantage. `prodTcrOutput` is a function of the whole outcome, secret key
included; an adversary that computes it from public data and oracle answers is not constructed
here.
-/

public section
namespace Qsag

set_option autoImplicit false

/-! ### Events defined from the extractor output -/

/-- The reduction run on one experiment outcome: `none` when the outcome is not a win. -/
def prodOutcomeBreak (suite : TweakableHashSuite) (params : PqHashParams)
    (hw : params.w = 4 ∨ params.w = 16) (o : ProdEufCmaOutcome)
    (hOneTime : params.statefulJorts = true →
      ∀ q, q ∈ o.queries → ∀ q', q' ∈ o.queries → q.epoch = q'.epoch → q = q') :
    Option (ProdBreakWitness suite params o.sk (productionSigningLog suite params o.sk o.queries)
      o.msgStar o.sigStar) :=
  if hWin : prodEufCmaWin suite params o = true then
    some (production_forgery_extract suite params o.sk o.queries o.msgStar o.sigStar hw hOneTime
      (fun e he hEq => by
        unfold prodEufCmaWin at hWin
        rw [Bool.and_eq_true] at hWin
        exact of_decide_eq_true hWin.2 (List.mem_map.mpr ⟨e, he, hEq⟩))
      (by
        unfold prodEufCmaWin at hWin
        rw [Bool.and_eq_true] at hWin
        exact hWin.1))
  else none

/-- Output of the target-collision reduction on one outcome: the chosen target and the colliding
    input, when the forgery leads to a collision. -/
def prodTcrOutput (suite : TweakableHashSuite) (params : PqHashParams)
    (hw : params.w = 4 ∨ params.w = 16) (o : ProdEufCmaOutcome)
    (hOneTime : params.statefulJorts = true →
      ∀ q, q ∈ o.queries → ∀ q', q' ∈ o.queries → q.epoch = q'.epoch → q = q') :
    Option (ProdTargetIdx × List UInt8) :=
  match prodOutcomeBreak suite params hw o hOneTime with
  | some (.tcr w) => some (w.target, w.forged)
  | _ => none

/-- Primitive target-collision win: `prodTcrCheck` on the returned pair. -/
def prodTcrEvent (suite : TweakableHashSuite) (params : PqHashParams)
    (hw : params.w = 4 ∨ params.w = 16) (o : ProdEufCmaOutcome)
    (hOneTime : params.statefulJorts = true →
      ∀ q, q ∈ o.queries → ∀ q', q' ∈ o.queries → q.epoch = q'.epoch → q = q') : Bool :=
  match prodTcrOutput suite params hw o hOneTime with
  | some (t, forged) => prodTcrCheck suite params o.sk o.sigStar.leafGlobalIdx t forged
  | none => false

/-- The reduction ends in the FORS index-coverage event. -/
def prodItsrEvent (suite : TweakableHashSuite) (params : PqHashParams)
    (hw : params.w = 4 ∨ params.w = 16) (o : ProdEufCmaOutcome)
    (hOneTime : params.statefulJorts = true →
      ∀ q, q ∈ o.queries → ∀ q', q' ∈ o.queries → q.epoch = q'.epoch → q = q') : Bool :=
  match prodOutcomeBreak suite params hw o hOneTime with
  | some (.itsr _) => true
  | _ => false

/-- The reduction ends in the preimage event. -/
def prodPreEvent (suite : TweakableHashSuite) (params : PqHashParams)
    (hw : params.w = 4 ∨ params.w = 16) (o : ProdEufCmaOutcome)
    (hOneTime : params.statefulJorts = true →
      ∀ q, q ∈ o.queries → ∀ q', q' ∈ o.queries → q.epoch = q'.epoch → q = q') : Bool :=
  match prodOutcomeBreak suite params hw o hOneTime with
  | some (.pre _) => true
  | _ => false

theorem prodOutcomeBreak_of_win (suite : TweakableHashSuite) (params : PqHashParams)
    (hw : params.w = 4 ∨ params.w = 16) (o : ProdEufCmaOutcome)
    (hOneTime : params.statefulJorts = true →
      ∀ q, q ∈ o.queries → ∀ q', q' ∈ o.queries → q.epoch = q'.epoch → q = q')
    (hWin : prodEufCmaWin suite params o = true)
    (hFresh : ∀ e ∈ productionSigningLog suite params o.sk o.queries, e.1 ≠ o.msgStar)
    (hAccept : verifyProductionPqHashSig suite params (derivePublicKey suite params o.sk)
      o.msgStar o.sigStar = true) :
    prodOutcomeBreak suite params hw o hOneTime =
      some (production_forgery_extract suite params o.sk o.queries o.msgStar o.sigStar hw hOneTime
        hFresh hAccept) := by
  unfold prodOutcomeBreak
  rw [dite_eq_left hWin]

theorem prodOutcomeBreak_of_not_win (suite : TweakableHashSuite) (params : PqHashParams)
    (hw : params.w = 4 ∨ params.w = 16) (o : ProdEufCmaOutcome)
    (hOneTime : params.statefulJorts = true →
      ∀ q, q ∈ o.queries → ∀ q', q' ∈ o.queries → q.epoch = q'.epoch → q = q')
    (hWin : ¬ prodEufCmaWin suite params o = true) :
    prodOutcomeBreak suite params hw o hOneTime = none := by
  unfold prodOutcomeBreak
  rw [dite_eq_right hWin]

theorem prodTcrOutput_eq (suite : TweakableHashSuite) (params : PqHashParams)
    (hw : params.w = 4 ∨ params.w = 16) (o : ProdEufCmaOutcome)
    (hOneTime : params.statefulJorts = true →
      ∀ q, q ∈ o.queries → ∀ q', q' ∈ o.queries → q.epoch = q'.epoch → q = q') :
    prodTcrOutput suite params hw o hOneTime =
      match prodOutcomeBreak suite params hw o hOneTime with
      | some (.tcr w) => some (w.target, w.forged)
      | _ => none := by
  rfl

theorem prodTcrEvent_eq (suite : TweakableHashSuite) (params : PqHashParams)
    (hw : params.w = 4 ∨ params.w = 16) (o : ProdEufCmaOutcome)
    (hOneTime : params.statefulJorts = true →
      ∀ q, q ∈ o.queries → ∀ q', q' ∈ o.queries → q.epoch = q'.epoch → q = q') :
    prodTcrEvent suite params hw o hOneTime =
      match prodTcrOutput suite params hw o hOneTime with
      | some (t, forged) => prodTcrCheck suite params o.sk o.sigStar.leafGlobalIdx t forged
      | none => false := by
  rfl

/-- A returned pair is a checked collision with an on-path target, at a hash call of the verifier
    on the forgery, and comes from a winning outcome. -/
theorem prodTcrOutput_sound (suite : TweakableHashSuite) (params : PqHashParams)
    (hw : params.w = 4 ∨ params.w = 16) (o : ProdEufCmaOutcome)
    (hOneTime : params.statefulJorts = true →
      ∀ q, q ∈ o.queries → ∀ q', q' ∈ o.queries → q.epoch = q'.epoch → q = q')
    (t : ProdTargetIdx) (forged : List UInt8)
    (hOut : prodTcrOutput suite params hw o hOneTime = some (t, forged)) :
    prodEufCmaWin suite params o = true ∧
    t.OnPath params (productionSigningLog suite params o.sk o.queries) o.sigStar.leafGlobalIdx
      (prodSigForsIdxs suite params (derivePublicKey suite params o.sk) o.msgStar o.sigStar) ∧
    t.ForgedCall suite params o.sk o.msgStar o.sigStar forged ∧
    prodTcrCheck suite params o.sk o.sigStar.leafGlobalIdx t forged = true := by
  unfold prodTcrOutput at hOut
  cases hB : prodOutcomeBreak suite params hw o hOneTime with
  | none => rw [hB] at hOut; cases hOut
  | some b =>
    rw [hB] at hOut
    have hWin : prodEufCmaWin suite params o = true := by
      unfold prodOutcomeBreak at hB
      split at hB
      · assumption
      · cases hB
    cases b with
    | itsr h => cases hOut
    | pre h => cases hOut
    | tcr w =>
      have hEq : (w.target, w.forged) = (t, forged) := Option.some.inj hOut
      have h1 : w.target = t := congrArg Prod.fst hEq
      have h2 : w.forged = forged := congrArg Prod.snd hEq
      rw [← h1, ← h2]
      exact ⟨hWin, w.onPath, w.call, w.check⟩

theorem prodItsrEvent_sound (suite : TweakableHashSuite) (params : PqHashParams)
    (hw : params.w = 4 ∨ params.w = 16) (o : ProdEufCmaOutcome)
    (hOneTime : params.statefulJorts = true →
      ∀ q, q ∈ o.queries → ∀ q', q' ∈ o.queries → q.epoch = q'.epoch → q = q')
    (hEv : prodItsrEvent suite params hw o hOneTime = true) :
    ProdForsItsrBreak suite params (derivePublicKey suite params o.sk)
      (productionSigningLog suite params o.sk o.queries) o.msgStar o.sigStar := by
  unfold prodItsrEvent at hEv
  cases hB : prodOutcomeBreak suite params hw o hOneTime with
  | none => rw [hB] at hEv; cases hEv
  | some b =>
    rw [hB] at hEv
    cases b with
    | itsr h => exact h
    | pre h => cases hEv
    | tcr w => cases hEv

theorem prodPreEvent_sound (suite : TweakableHashSuite) (params : PqHashParams)
    (hw : params.w = 4 ∨ params.w = 16) (o : ProdEufCmaOutcome)
    (hOneTime : params.statefulJorts = true →
      ∀ q, q ∈ o.queries → ∀ q', q' ∈ o.queries → q.epoch = q'.epoch → q = q')
    (hEv : prodPreEvent suite params hw o hOneTime = true) :
    ProdPreimageBreak suite params o.sk (productionSigningLog suite params o.sk o.queries)
      o.msgStar o.sigStar := by
  unfold prodPreEvent at hEv
  cases hB : prodOutcomeBreak suite params hw o hOneTime with
  | none => rw [hB] at hEv; cases hEv
  | some b =>
    rw [hB] at hEv
    cases b with
    | itsr h => cases hEv
    | pre h => exact h
    | tcr w => cases hEv

/-- Every winning outcome lands in one of the three extractor-defined events. -/
theorem prodEufCmaWin_classified (suite : TweakableHashSuite) (params : PqHashParams)
    (hw : params.w = 4 ∨ params.w = 16) (o : ProdEufCmaOutcome)
    (hOneTime : params.statefulJorts = true →
      ∀ q, q ∈ o.queries → ∀ q', q' ∈ o.queries → q.epoch = q'.epoch → q = q')
    (hWin : prodEufCmaWin suite params o = true) :
    prodItsrEvent suite params hw o hOneTime = true ∨
    prodTcrEvent suite params hw o hOneTime = true ∨
    prodPreEvent suite params hw o hOneTime = true := by
  cases hB : prodOutcomeBreak suite params hw o hOneTime with
  | none =>
    exfalso
    unfold prodOutcomeBreak at hB
    split at hB
    · cases hB
    · rename_i hNo
      exact hNo hWin
  | some b =>
    cases b with
    | itsr h =>
      left
      unfold prodItsrEvent
      rw [hB]
    | pre h =>
      right; right
      unfold prodPreEvent
      rw [hB]
    | tcr w =>
      right; left
      unfold prodTcrEvent prodTcrOutput
      rw [hB]
      exact w.check

/-- **Production EUF-CMA count against extractor-defined events.** The number of winning coins is
    at most the number of coins on which the reduction ends in index coverage, plus the number on
    which the pair it returns passes `prodTcrCheck`, plus the number on which it ends in the
    preimage event. Unlike `production_euf_cma_advantage_bound` there is no supplied event and no
    hypothesis covering `ProdSmTcrBreak`. -/
theorem production_euf_cma_extracted_bound {Ω : Type} (suite : TweakableHashSuite)
    (params : PqHashParams) (hw : params.w = 4 ∨ params.w = 16)
    (coins : List Ω) (game : Ω → ProdEufCmaOutcome)
    (hOneTime : ∀ ω, params.statefulJorts = true → ∀ q, q ∈ (game ω).queries →
      ∀ q', q' ∈ (game ω).queries → q.epoch = q'.epoch → q = q') :
    hitCount (fun ω => prodEufCmaWin suite params (game ω)) coins ≤
      hitCount (fun ω => prodItsrEvent suite params hw (game ω) (hOneTime ω)) coins +
      hitCount (fun ω => prodTcrEvent suite params hw (game ω) (hOneTime ω)) coins +
      hitCount (fun ω => prodPreEvent suite params hw (game ω) (hOneTime ω)) coins :=
  hitCount_union_bound _ _ _ _
    (fun ω hWin => prodEufCmaWin_classified suite params hw (game ω) (hOneTime ω) hWin) coins

end Qsag
end

#verify_constructive Qsag.prodTcrOutput_sound Qsag.prodItsrEvent_sound Qsag.prodPreEvent_sound
#verify_constructive Qsag.prodEufCmaWin_classified Qsag.production_euf_cma_extracted_bound

/-!
# Qsag.Protocol.Signing.ProdCollisionAccounting — the candidate targets of one forgery

`ProdSmTcrBreak` ranges over every honest hash input of the key. A returned `ProdTcrWitness` is
narrower: `ProdTargetIdx.OnPath` leaves no free index. `prodPathTargets` lists the candidates for
a forgery with hypertree leaf `leaf` and FORS indices `idxs`:

* per layer, the `subtreeHeight` XMSS nodes on the path, one WOTS public-key compression and
  `ell1 * (w - 1)` chain steps;
* per FORS tree, the `forsHeight` nodes on the path of its opened leaf, and one root compression;
* per logged signature, its `numLayers` layer digests and its message pre-hash.

`ProdTargetIdx.mem_pathTargets` shows every on-path target is in the list and
`prodPathTargets_length` gives its length `prodPathTargetCount params log.length`.
`prodTcrOutput_target_budget` states both for the pair the reduction returns, with the log length
bounded by the number of signing queries.

Scope and limits.
* The list depends on the leaf and FORS indices of the forgery, which the adversary chooses after
  seeing signatures. This is a bound on the targets *selected by one forgery*, not on a target set
  fixed before the experiment. Over all leaves the node, compression and chain targets range over
  the whole hypertree and FORS forest of the key.
* In stateless profiles an on-path node need not have been evaluated by any signing query: it is
  determined by the secret key, not by the log.
* No count of hash evaluations made by the extractor is proved, and no probability is assigned.
-/

public section
namespace Qsag

set_option autoImplicit false

-- FORS tree address, key pair and leaf indices of the forgery.
set_option hygiene false in
local notation:max "FORS_TREE" => (UInt64.ofNat (sigStar.leafGlobalIdx / 2 ^ params.subtreeHeight))
set_option hygiene false in
local notation:max "FORS_KP" => (sigStar.leafGlobalIdx % 2 ^ params.subtreeHeight)
set_option hygiene false in
local notation:max "FORS_IDXS" =>
  (prodSigForsIdxs suite params (derivePublicKey suite params sk) msgStar sigStar)

theorem prod_length_flatMap_const {α β : Type} (f : α → List β) (k : Nat) :
    ∀ (xs : List α), (∀ x ∈ xs, (f x).length = k) → (xs.flatMap f).length = xs.length * k
  | [], _ => by rw [List.flatMap_nil, List.length_nil, List.length_nil, Nat.zero_mul]
  | x :: xs, h => by
    rw [List.flatMap_cons, List.length_append, h x List.mem_cons_self,
      prod_length_flatMap_const f k xs (fun y hy => h y (List.mem_cons_of_mem x hy)),
      List.length_cons, Nat.succ_mul, Nat.add_comm]

theorem prod_length_range_flatMap_map {β : Type} (n k : Nat) (g : Nat → Nat → β) :
    ((List.range n).flatMap fun x => (List.range k).map (g x)).length = n * k := by
  rw [prod_length_flatMap_const _ k _ (fun x _ => by rw [List.length_map, List.length_range]),
    List.length_range]

theorem prod_length_range_flatMap_flatMap_map {β : Type} (n m k : Nat) (g : Nat → Nat → Nat → β) :
    ((List.range n).flatMap fun x => (List.range m).flatMap fun y =>
      (List.range k).map (g x y)).length = n * (m * k) := by
  rw [prod_length_flatMap_const _ (m * k) _
      (fun x _ => prod_length_range_flatMap_map m k (g x)),
    List.length_range]

theorem prod_length_flatMap_range_map {α β : Type} (xs : List α) (k : Nat) (g : α → Nat → β) :
    (xs.flatMap fun e => (List.range k).map (g e)).length = xs.length * k :=
  prod_length_flatMap_const _ k xs (fun x _ => by rw [List.length_map, List.length_range])

/-- Honest hash inputs on the verification path of a forgery with leaf `leaf` and FORS leaf
    indices `idxs`, over the log `log`. -/
def prodPathTargets (params : PqHashParams) (log : List (List UInt8 × PqHashSig)) (leaf : Nat)
    (idxs : List Nat) : List ProdTargetIdx :=
  ((List.range params.numLayers).flatMap fun l => (List.range params.subtreeHeight).map fun h =>
    ProdTargetIdx.xmssNode l h
      (leaf / 2 ^ (l * params.subtreeHeight) % 2 ^ params.subtreeHeight / 2 ^ (h + 1))) ++
  ((List.range params.numLayers).map ProdTargetIdx.wotsPk ++
  (((List.range params.numLayers).flatMap fun l => (List.range params.ell1).flatMap fun r =>
    (List.range (params.w - 1)).map fun s => ProdTargetIdx.chainStep l r s) ++
  (((List.range params.forsTrees).flatMap fun j => (List.range params.forsHeight).map fun h =>
    ProdTargetIdx.forsNode j h (params.forsHeight - (h + 1)) (idxs.getD j 0 / 2 ^ (h + 1))) ++
  (ProdTargetIdx.forsRoots ::
  ((log.flatMap fun e => (List.range params.numLayers).map fun i =>
    ProdTargetIdx.signedDigest e i) ++
  log.map ProdTargetIdx.preHash)))))

/-- Number of candidate targets of one forgery against a log of `logLen` signatures. -/
def prodPathTargetCount (params : PqHashParams) (logLen : Nat) : Nat :=
  params.numLayers * params.subtreeHeight +
  (params.numLayers +
  (params.numLayers * (params.ell1 * (params.w - 1)) +
  (params.forsTrees * params.forsHeight +
  (logLen * params.numLayers + logLen + 1))))

theorem prodPathTargetCount_eq (params : PqHashParams) (logLen : Nat) :
    prodPathTargetCount params logLen =
      params.numLayers * params.subtreeHeight +
      (params.numLayers +
      (params.numLayers * (params.ell1 * (params.w - 1)) +
      (params.forsTrees * params.forsHeight +
      (logLen * params.numLayers + logLen + 1)))) := by
  rfl

theorem prodPathTargets_length (params : PqHashParams) (log : List (List UInt8 × PqHashSig))
    (leaf : Nat) (idxs : List Nat) :
    (prodPathTargets params log leaf idxs).length = prodPathTargetCount params log.length := by
  unfold prodPathTargets prodPathTargetCount
  simp only [List.length_append, List.length_cons, List.length_map, List.length_range,
    prod_length_range_flatMap_flatMap_map, prod_length_flatMap_range_map]

theorem prodPathTargetCount_mono (params : PqHashParams) {a b : Nat} (h : a ≤ b) :
    prodPathTargetCount params a ≤ prodPathTargetCount params b := by
  unfold prodPathTargetCount
  have h1 : a * params.numLayers ≤ b * params.numLayers := Nat.mul_le_mul_right _ h
  omega

/-- Every on-path target is one of the listed candidates. -/
theorem ProdTargetIdx.mem_pathTargets (params : PqHashParams)
    (log : List (List UInt8 × PqHashSig)) (leaf : Nat) (idxs : List Nat) :
    ∀ t : ProdTargetIdx, t.OnPath params log leaf idxs → t ∈ prodPathTargets params log leaf idxs
  | .xmssNode l h n, hOn => by
    obtain ⟨hl, hh, hLo, hHi⟩ := hOn
    have hn : leaf / 2 ^ (l * params.subtreeHeight) % 2 ^ params.subtreeHeight / 2 ^ (h + 1) = n :=
      Nat.div_eq_of_lt_le hLo hHi
    unfold prodPathTargets
    apply List.mem_append_left
    exact List.mem_flatMap.mpr ⟨l, List.mem_range.mpr hl,
      List.mem_map.mpr ⟨h, List.mem_range.mpr hh, by rw [hn]⟩⟩
  | .wotsPk l, hOn => by
    unfold prodPathTargets
    apply List.mem_append_right
    apply List.mem_append_left
    exact List.mem_map.mpr ⟨l, List.mem_range.mpr hOn, rfl⟩
  | .chainStep l r s, hOn => by
    obtain ⟨hl, hr, hs⟩ := hOn
    unfold prodPathTargets
    apply List.mem_append_right
    apply List.mem_append_right
    apply List.mem_append_left
    exact List.mem_flatMap.mpr ⟨l, List.mem_range.mpr hl,
      List.mem_flatMap.mpr ⟨r, List.mem_range.mpr hr,
        List.mem_map.mpr ⟨s, List.mem_range.mpr hs, rfl⟩⟩⟩
  | .forsNode j h d b, hOn => by
    obtain ⟨_, hj, hD, hLo, hHi⟩ := hOn
    have hb : idxs.getD j 0 / 2 ^ (h + 1) = b := Nat.div_eq_of_lt_le hLo hHi
    have hd : params.forsHeight - (h + 1) = d := by rw [← hD, Nat.add_sub_cancel]
    have hh : h < params.forsHeight := by
      rw [← hD]
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self h) (Nat.le_add_left _ _)
    unfold prodPathTargets
    apply List.mem_append_right
    apply List.mem_append_right
    apply List.mem_append_right
    apply List.mem_append_left
    exact List.mem_flatMap.mpr ⟨j, List.mem_range.mpr hj,
      List.mem_map.mpr ⟨h, List.mem_range.mpr hh, by rw [hd, hb]⟩⟩
  | .forsRoots, hOn => by
    have _hSt : params.statefulJorts = false := hOn
    unfold prodPathTargets
    apply List.mem_append_right
    apply List.mem_append_right
    apply List.mem_append_right
    apply List.mem_append_right
    exact List.mem_cons_self
  | .signedDigest e i, hOn => by
    obtain ⟨he, hi, _⟩ := hOn
    unfold prodPathTargets
    apply List.mem_append_right
    apply List.mem_append_right
    apply List.mem_append_right
    apply List.mem_append_right
    apply List.mem_cons_of_mem
    apply List.mem_append_left
    exact List.mem_flatMap.mpr ⟨e, he, List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩⟩
  | .preHash e, hOn => by
    obtain ⟨he, _⟩ := hOn
    unfold prodPathTargets
    apply List.mem_append_right
    apply List.mem_append_right
    apply List.mem_append_right
    apply List.mem_append_right
    apply List.mem_cons_of_mem
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨e, he, rfl⟩

theorem productionSigningLog_length_le (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) :
    ∀ queries : List ProdSigningQuery,
      (productionSigningLog suite params sk queries).length ≤ queries.length
  | [] => Nat.le_refl 0
  | q :: qs => by
    have ih := productionSigningLog_length_le suite params sk qs
    unfold productionSigningLog
    cases prodSignQuery suite params sk q with
    | none => exact Nat.le_trans ih (Nat.le_succ _)
    | some sig => exact Nat.succ_le_succ ih

/-- The target of a returned witness is one of the candidates of its forgery. -/
theorem ProdTcrWitness.target_mem {suite : TweakableHashSuite} {params : PqHashParams}
    {sk : PqSecretKey} {log : List (List UInt8 × PqHashSig)} {msgStar : List UInt8}
    {sigStar : PqHashSig} (w : ProdTcrWitness suite params sk log msgStar sigStar) :
    w.target ∈ prodPathTargets params log sigStar.leafGlobalIdx (FORS_IDXS) :=
  ProdTargetIdx.mem_pathTargets params log _ _ w.target w.onPath

/-- **Target budget of the returned pair.** The target returned on an experiment outcome is one
    of the listed candidates of that forgery, a checked collision with it, and the number of
    candidates is at most `prodPathTargetCount params (number of signing queries)`. -/
theorem prodTcrOutput_target_budget (suite : TweakableHashSuite) (params : PqHashParams)
    (hw : params.w = 4 ∨ params.w = 16) (o : ProdEufCmaOutcome)
    (hOneTime : params.statefulJorts = true →
      ∀ q, q ∈ o.queries → ∀ q', q' ∈ o.queries → q.epoch = q'.epoch → q = q')
    (t : ProdTargetIdx) (forged : List UInt8)
    (hOut : prodTcrOutput suite params hw o hOneTime = some (t, forged)) :
    t ∈ prodPathTargets params (productionSigningLog suite params o.sk o.queries)
      o.sigStar.leafGlobalIdx
      (prodSigForsIdxs suite params (derivePublicKey suite params o.sk) o.msgStar o.sigStar) ∧
    (prodPathTargets params (productionSigningLog suite params o.sk o.queries)
      o.sigStar.leafGlobalIdx
      (prodSigForsIdxs suite params (derivePublicKey suite params o.sk) o.msgStar
        o.sigStar)).length ≤ prodPathTargetCount params o.queries.length ∧
    prodTcrCheck suite params o.sk o.sigStar.leafGlobalIdx t forged = true := by
  obtain ⟨_, hOn, _, hChk⟩ := prodTcrOutput_sound suite params hw o hOneTime t forged hOut
  refine ⟨ProdTargetIdx.mem_pathTargets params _ _ _ t hOn, ?_, hChk⟩
  rw [prodPathTargets_length]
  exact prodPathTargetCount_mono params (productionSigningLog_length_le suite params o.sk o.queries)

/-- An out-of-range layer is not a candidate target: the bound is not vacuous. -/
theorem prodTargetIdx_layer_out_of_range (params : PqHashParams)
    (log : List (List UInt8 × PqHashSig)) (leaf : Nat) (idxs : List Nat) (layer : Nat)
    (hLayer : params.numLayers ≤ layer) :
    ¬ (ProdTargetIdx.wotsPk layer).OnPath params log leaf idxs :=
  fun hOn => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hOn hLayer)

end Qsag
end

#verify_constructive Qsag.prodPathTargets_length Qsag.prodPathTargetCount_mono
#verify_constructive Qsag.ProdTargetIdx.mem_pathTargets Qsag.productionSigningLog_length_le
#verify_constructive Qsag.ProdTcrWitness.target_mem Qsag.prodTcrOutput_target_budget
#verify_constructive Qsag.prodTargetIdx_layer_out_of_range
