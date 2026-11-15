module
public import Qsag.Protocol.Threshold.ThresholdMpc
import all Qsag.Protocol.Threshold.ThresholdMpc
import all Qsag.Protocol.Signing.HashSigs
import all Qsag.Protocol.Aggregation.UcGames
import Qsag.Tactic.AssuranceKit

/-!
Demand-driven public production-signing control. Query constructors are the actual
production cut operations, not raw secret PRF requests. A suspended continuation
contains only public control and earlier cut answers, never a signing key. The
interpreter theorem is parametric in the actual existing production oracle record.
Active checks must authorize an answer before the continuation is resumed.
-/
public section
namespace Qsag.RssSigning
set_option autoImplicit false

inductive Query where
  | prfMsg (optRand mu : List UInt8)
  | wotsChain (layer : UInt32) (tree : UInt64) (kp chain steps : Nat)
  | forsReveal (tree : UInt64) (kp treeNumber leaf : Nat)
  | forsLeaf (tree : UInt64) (kp treeNumber leaf : Nat)
  deriving DecidableEq, Repr

abbrev Bytes := List UInt8
abbrev Program (α : Type) := OracleComp Query Bytes α

def answer (o : ProductionPqHashMpcOracles) : Query → Bytes
  | .prfMsg rand mu => o.evalPrfMsg rand mu
  | .wotsChain layer tree kp chain steps => o.evalWotsChainEnd layer tree kp chain steps
  | .forsReveal tree kp j u => o.evalIndexedForsReveal tree kp j u
  | .forsLeaf tree kp j u => o.evalIndexedForsLeafHash tree kp j u

def bind {α β : Type} : Program α → (α → Program β) → Program β
  | .pure x, k => k x
  | .query q next, k => .query q (fun result => bind (next result) k)

instance : Monad Program where
  pure := OracleComp.pure
  bind := bind

def ask (q : Query) : Program Bytes := .query q .pure

def evaluate {α : Type} (o : ProductionPqHashMpcOracles) (program : Program α) : α :=
  evalOracleComp (answer o) program

@[simp] theorem evaluate_pure {α : Type} (o : ProductionPqHashMpcOracles) (x : α) :
    evaluate o (pure x : Program α) = x := by rfl

@[simp] theorem evaluate_bind {α β : Type} (o : ProductionPqHashMpcOracles)
    (p : Program α) (k : α → Program β) :
    evaluate o (p >>= k) = evaluate o (k (evaluate o p)) := by
  induction p with
  | pure x => rfl
  | query q next ih => exact ih (answer o q)

@[simp] theorem evaluate_ask (o : ProductionPqHashMpcOracles) (q : Query) :
    evaluate o (ask q) = answer o q := by rfl

def mapProgram {α β : Type} (f : α → Program β) : List α → Program (List β)
  | [] => pure []
  | x :: xs => do
      let y ← f x
      let ys ← mapProgram f xs
      pure (y :: ys)

@[simp] theorem evaluate_mapProgram {α β : Type} (o : ProductionPqHashMpcOracles)
    (f : α → Program β) (xs : List α) :
    evaluate o (mapProgram f xs) = xs.map (fun x => evaluate o (f x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [mapProgram, evaluate_bind, evaluate_pure, ih, List.map_cons]

def merkle (suite : TweakableHashSuite) (pkSeed : Bytes) (layer : UInt32)
    (tree : UInt64) (kind : AdrsKind) (leaf : Nat → Program Bytes) :
    Nat → Nat → Program Bytes
  | 0, index => leaf index
  | height + 1, index => do
      let left ← merkle suite pkSeed layer tree kind leaf height (2 * index)
      let right ← merkle suite pkSeed layer tree kind leaf height (2 * index + 1)
      pure (thNodeH suite pkSeed ⟨layer, tree, kind, 0, UInt32.ofNat (height + 1),
        UInt32.ofNat index⟩ left right)

@[simp] theorem evaluate_merkle (o : ProductionPqHashMpcOracles) (suite : TweakableHashSuite)
    (pkSeed : Bytes) (layer : UInt32) (tree : UInt64) (kind : AdrsKind)
    (leaf : Nat → Program Bytes) (height index : Nat) :
    evaluate o (merkle suite pkSeed layer tree kind leaf height index) =
      computeMerkleNode suite pkSeed layer tree kind (fun j => evaluate o (leaf j)) height index := by
  induction height generalizing index with
  | zero => rfl
  | succ height ih => simp only [merkle, evaluate_bind, evaluate_pure, ih, computeMerkleNode]

def merkleKp (suite : TweakableHashSuite) (pkSeed : Bytes) (layer : UInt32)
    (tree : UInt64) (kind : AdrsKind) (kp : UInt32) (leaf : Nat → Program Bytes) :
    Nat → Nat → Nat → Program Bytes
  | 0, _, base => leaf base
  | height + 1, index, base => do
      let left ← merkleKp suite pkSeed layer tree kind kp leaf height (2 * index) (2 * base)
      let right ← merkleKp suite pkSeed layer tree kind kp leaf height (2 * index + 1) (2 * base + 1)
      pure (thNodeH suite pkSeed ⟨layer, tree, kind, kp, UInt32.ofNat (height + 1),
        UInt32.ofNat index⟩ left right)

@[simp] theorem evaluate_merkleKp (o : ProductionPqHashMpcOracles) (suite : TweakableHashSuite)
    (pkSeed : Bytes) (layer : UInt32) (tree : UInt64) (kind : AdrsKind) (kp : UInt32)
    (leaf : Nat → Program Bytes) (height index base : Nat) :
    evaluate o (merkleKp suite pkSeed layer tree kind kp leaf height index base) =
      computeMerkleNodeKp suite pkSeed layer tree kind kp (fun j => evaluate o (leaf j))
        height index base := by
  induction height generalizing index base with
  | zero => rfl
  | succ height ih => simp only [merkleKp, evaluate_bind, evaluate_pure, ih, computeMerkleNodeKp]

def authPath (suite : TweakableHashSuite) (pkSeed : Bytes) (layer : UInt32)
    (tree : UInt64) (kind : AdrsKind) (kp : UInt32) (leaf : Nat → Program Bytes) :
    Nat → Nat → Nat → Nat → Program (List Bytes)
  | 0, _, _, _ => pure []
  | height + 1, index, base, localIndex =>
      if localIndex < 2 ^ height then do
        let sibling ← merkleKp suite pkSeed layer tree kind kp leaf height (2 * index + 1) (2 * base + 1)
        let path ← authPath suite pkSeed layer tree kind kp leaf height (2 * index) (2 * base) localIndex
        pure (sibling :: path)
      else do
        let sibling ← merkleKp suite pkSeed layer tree kind kp leaf height (2 * index) (2 * base)
        let path ← authPath suite pkSeed layer tree kind kp leaf height (2 * index + 1)
          (2 * base + 1) (localIndex - 2 ^ height)
        pure (sibling :: path)

@[simp] theorem evaluate_authPath (o : ProductionPqHashMpcOracles) (suite : TweakableHashSuite)
    (pkSeed : Bytes) (layer : UInt32) (tree : UInt64) (kind : AdrsKind) (kp : UInt32)
    (leaf : Nat → Program Bytes) (height index base localIndex : Nat) :
    evaluate o (authPath suite pkSeed layer tree kind kp leaf height index base localIndex) =
      buildMerkleAuthPathKp suite pkSeed layer tree kind kp (fun j => evaluate o (leaf j))
        height index base localIndex := by
  induction height generalizing index base localIndex with
  | zero => rfl
  | succ height ih =>
      simp only [authPath, buildMerkleAuthPathKp]
      split <;> simp only [evaluate_bind, evaluate_merkleKp, evaluate_pure, ih]

def wotsPk (suite : TweakableHashSuite) (params : PqHashParams) (pkSeed : Bytes)
    (layer : UInt32) (tree : UInt64) (kp : Nat) : Program Bytes := do
  let chains ← mapProgram (fun r => ask (.wotsChain layer tree kp r (params.w - 1)))
    (List.range params.ell1)
  pure (thTweakTl suite pkSeed ⟨layer, tree, .wotsPk, UInt32.ofNat kp, 0, 0⟩ chains)

@[simp] theorem evaluate_wotsPk (o : ProductionPqHashMpcOracles) (suite : TweakableHashSuite)
    (params : PqHashParams) (pkSeed : Bytes) (layer : UInt32) (tree : UInt64) (kp : Nat) :
    evaluate o (wotsPk suite params pkSeed layer tree kp) =
      mpcComputeWotsPk suite params o.toPqHashMpcOracles pkSeed layer tree kp := by
  simp only [wotsPk, evaluate_bind, evaluate_mapProgram, evaluate_ask, evaluate_pure,
    answer, mpcComputeWotsPk]

def xmssRoot (suite : TweakableHashSuite) (params : PqHashParams) (pkSeed : Bytes)
    (layer : UInt32) (tree : UInt64) : Program Bytes :=
  merkle suite pkSeed layer tree .tree (wotsPk suite params pkSeed layer tree) params.subtreeHeight 0

@[simp] theorem evaluate_xmssRoot (o : ProductionPqHashMpcOracles) (suite : TweakableHashSuite)
    (params : PqHashParams) (pkSeed : Bytes) (layer : UInt32) (tree : UInt64) :
    evaluate o (xmssRoot suite params pkSeed layer tree) =
      mpcComputeXmssSubtreeRoot suite params o.toPqHashMpcOracles pkSeed layer tree := by
  simp only [xmssRoot, evaluate_merkle, evaluate_wotsPk, mpcComputeXmssSubtreeRoot]

def publicKey (suite : TweakableHashSuite) (params : PqHashParams) (pkSeed : Bytes) :
    Program PqPublicKey := do
  let root ← xmssRoot suite params pkSeed (UInt32.ofNat (params.numLayers - 1)) 0
  pure ⟨pkSeed, root⟩

@[simp] theorem evaluate_publicKey (o : ProductionPqHashMpcOracles) (suite : TweakableHashSuite)
    (params : PqHashParams) (pkSeed : Bytes) :
    evaluate o (publicKey suite params pkSeed) =
      derivePublicKeyMpc suite params o.toPqHashMpcOracles pkSeed := by
  simp only [publicKey, evaluate_bind, evaluate_pure, evaluate_xmssRoot, derivePublicKeyMpc]

#verify_constructive evaluate_pure evaluate_bind evaluate_ask evaluate_mapProgram
  evaluate_merkle evaluate_merkleKp evaluate_authPath evaluate_wotsPk evaluate_xmssRoot evaluate_publicKey
end Qsag.RssSigning
