module
public import Qsag.HypertreeEufCma
import all Qsag.HypertreeEufCma
import all Qsag.HashSigs
import Qsag.Tactic.AssuranceKit

/-!
# Qsag.ProdCollisionWitness — returned collision witnesses for the production verifier

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

/-- Index bounds and path provenance of a target, for a forgery with hypertree leaf `leaf` and
    FORS leaf indices `idxs` over the signing log `log`. -/
@[reducible] def ProdTargetIdx.OnPath (params : PqHashParams) (log : List (List UInt8 × PqHashSig))
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
@[reducible] def ProdTargetIdx.ForgedCall (suite : TweakableHashSuite) (params : PqHashParams)
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
def prodWalkMerkleExtract (suite : TweakableHashSuite) (pkSeed : List UInt8)
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
        simp only [walkMerkleAuthPath, computeMerkleNode, Option.some.injEq] at hW
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
            simp only [walkMerkleAuthPath, hHalf, ↓reduceIte, hSub, Option.some.injEq] at hW
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
            simp only [walkMerkleAuthPath, hHalf, ↓reduceIte, hSub, Option.some.injEq] at hW
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
def prodWalkMerkleKpExtract (suite : TweakableHashSuite) (pkSeed : List UInt8)
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
        simp only [walkMerkleAuthPathKp, computeMerkleNodeKp, Option.some.injEq] at hW
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
            simp only [walkMerkleAuthPathKp, computeMerkleNodeKp, hHalf, ↓reduceIte, hSub,
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
            simp only [walkMerkleAuthPathKp, computeMerkleNodeKp, hHalf, ↓reduceIte, hSub,
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
def prodChainExtract (suite : TweakableHashSuite) (sk : PqSecretKey)
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
def prodAllChainsExtract (suite : TweakableHashSuite) (params : PqHashParams)
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
