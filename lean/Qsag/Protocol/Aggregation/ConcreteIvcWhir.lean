module
public import Qsag.Protocol.Aggregation.ConcreteIvcSumcheck
public import Qsag.Protocol.Aggregation.WhirAssignmentRecovery
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag.MultiDepthQrom.IvcAlgebra
open Qsag
attribute [-instance] Fin.instLinearOrderPackage
set_option autoImplicit false

local infixl:65 " +ₑ " => QuinticGoldilocks.add
local infixl:65 " -ₑ " => QuinticGoldilocks.sub
local infixl:70 " *ₑ " => QuinticGoldilocks.mul

structure FoldChallenges where
  theta : E
  alpha : E
  beta : E
  deriving Inhabited

structure Kernel where
  claim : E
  tensorWeight : E
  remaining : List E
  points : List (E × E)

def beginFold (ro : RO) (se t01 t10 : E) : Fs E := do
  -- "FOLD_A", "FOLD_PHI"
  absorb ro [70, 79, 76, 68, 95, 65] (exts [se,t01,t10])
  challenge ro [70, 79, 76, 68, 95, 80, 72, 73]

def finishFold (ro : RO) (k : Kernel) (se t01 t10 cf cg phi : E) : Fs (Kernel × FoldChallenges) := do
  let r :: rest := k.remaining | failure
  -- "FOLD_B", "FOLD_THETA", "FOLD_ALPHA", "FOLD_BETA"
  absorb ro [70, 79, 76, 68, 95, 66] (exts [cf,cg])
  let theta ← challenge ro [70, 79, 76, 68, 95, 84, 72, 69, 84, 65]
  let alpha ← challenge ro [70, 79, 76, 68, 95, 65, 76, 80, 72, 65]
  let beta ← challenge ro [70, 79, 76, 68, 95, 66, 69, 84, 65]
  let f := se +ₑ phi *ₑ t01
  let g := t10 +ₑ phi *ₑ (k.claim -ₑ se)
  return (⟨g +ₑ alpha *ₑ (f +ₑ theta *ₑ g) +ₑ beta *ₑ (cf +ₑ theta *ₑ cg),
    k.tensorWeight *ₑ (.one +ₑ phi *ₑ r), rest,
    k.points.map (fun (w,x) => (w *ₑ (.one +ₑ phi *ₑ x), x *ₑ x))⟩, ⟨theta,alpha,beta⟩)

@[expose] def foldKernel (ro : RO) (k : Kernel) (wire : List E) : Fs (Kernel × FoldChallenges) := do
  let extsInline (vs : List E) := NodeWire.words (vs.flatMap fun v => [v.c0,v.c1,v.c2,v.c3,v.c4])
  let [se,t01,t10,cf,cg] := wire | (fun _ => none)
  -- "FOLD_A", "FOLD_PHI"
  absorb ro [70, 79, 76, 68, 95, 65] (extsInline [se,t01,t10]) false
  let phi ← challenge ro [70, 79, 76, 68, 95, 80, 72, 73] false
  let r :: rest := k.remaining | (fun _ => none)
  -- "FOLD_B", "FOLD_THETA", "FOLD_ALPHA", "FOLD_BETA"
  absorb ro [70, 79, 76, 68, 95, 66] (extsInline [cf,cg]) false
  let theta ← challenge ro [70, 79, 76, 68, 95, 84, 72, 69, 84, 65] false
  let alpha ← challenge ro [70, 79, 76, 68, 95, 65, 76, 80, 72, 65] false
  let beta ← challenge ro [70, 79, 76, 68, 95, 66, 69, 84, 65] false
  let f := se +ₑ phi *ₑ t01
  let g := t10 +ₑ phi *ₑ (k.claim -ₑ se)
  return (⟨g +ₑ alpha *ₑ (f +ₑ theta *ₑ g) +ₑ beta *ₑ (cf +ₑ theta *ₑ cg),
    k.tensorWeight *ₑ (.one +ₑ phi *ₑ r), rest,
    k.points.map (fun (w,x) => (w *ₑ (.one +ₑ phi *ₑ x), x *ₑ x))⟩, ⟨theta,alpha,beta⟩)

@[expose] def subgroupGenerator (log : Nat) : Nat :=
  powMod 1753635133440165772 (2 ^ (32 - log)) goldilocksPrime

def evenOdd (a b : E) (x : Nat) : E × E :=
  let half := base 9223372034707292161
  let invX := base (powMod x (goldilocksPrime - 2) goldilocksPrime)
  ((a +ₑ b) *ₑ half, (a -ₑ b) *ₑ half *ₑ invX)

/-- Basic even/odd polynomial fold. The masked affine fold uses the same two evaluations. -/
def binaryFold (a b : E) (x : Nat) (alpha : E) : E × E :=
  let (even,odd) := evenOdd a b x
  (even +ₑ alpha *ₑ odd, odd)

@[expose] def foldFiber (vals : List E) (x : Nat) (chals : List FoldChallenges) : Option (E × E) := do
  let halfInv : E := .ofBase (Goldilocks.ofNat 9223372034707292161)
  let _ ← if x != 0 && vals.length == 2 ^ chals.length then some () else none
  let mut pairs := vals
  let mut x0 := x
  let mut zeta := subgroupGenerator chals.length
  for c in chals do
    let half := pairs.length / 2
    let mut values := []
    let mut xi := x0
    for (a,b) in (pairs.take half).zip (pairs.drop half) do
      let invXi : E := .ofBase (Goldilocks.ofNat (powMod xi (goldilocksPrime - 2) goldilocksPrime))
      let even := (a +ₑ b) *ₑ halfInv
      let odd := (a -ₑ b) *ₑ halfInv *ₑ invXi
      let mix := even +ₑ c.theta *ₑ odd
      values := (odd +ₑ (c.alpha +ₑ c.beta *ₑ .ofBase (Goldilocks.ofNat (xi * xi % goldilocksPrime))) *ₑ mix) :: values
      xi := xi * zeta % goldilocksPrime
    pairs := values.reverse
    x0 := x0 * x0 % goldilocksPrime
    zeta := zeta * zeta % goldilocksPrime
  let [out] := pairs | none
  return (.ofBase (Goldilocks.ofNat x0), out)

def fiberLeaf (stage idx : Nat) (nonce : BitVec 256) (ws : List Goldilocks) : Spec.Bytes :=
  -- "IVC-FIBER-LEAF"
  encodeMultiFrame [[73, 86, 67, 45, 70, 73, 66, 69, 82, 45, 76, 69, 65, 70], leb128 stage, leb128 idx,
    encodeNatLeBytes 32 nonce.toNat, NodeWire.words ws]

def fiberParent (stage level : Nat) (left right : Spec.Bytes) := encodeMultiFrame
  -- "IVC-FIBER-NODE"
  [[73, 86, 67, 45, 70, 73, 66, 69, 82, 45, 78, 79, 68, 69], leb128 stage, leb128 level, left, right]

@[expose] def fiberPath (ro : RO) (stage idx : Nat) (nonce : BitVec 256)
    (ws : List Goldilocks) (siblings : List (List Goldilocks)) : Spec.Bytes :=
  -- "IVC-FIBER-LEAF"
  let leaf := encodeMultiFrame [[73, 86, 67, 45, 70, 73, 66, 69, 82, 45, 76, 69, 65, 70], leb128 stage, leb128 idx,
    encodeNatLeBytes 32 nonce.toNat, NodeWire.words ws]
  siblings.zipIdx.foldl (fun cur (s, level) =>
    let sibling := NodeWire.words s
    let (l, r) := if idx.testBit level then (sibling, cur) else (cur, sibling)
    -- "IVC-FIBER-NODE"
    ro (encodeMultiFrame [[73, 86, 67, 45, 70, 73, 66, 69, 82, 45, 78, 79, 68, 69], leb128 stage, leb128 level, l, r])) (ro leaf)

/-- Partial Fisher–Yates with a sparse map of the locations touched so far. -/
def queryIndices (ro : RO) (height count : Nat) : Fs (List Nat) := do
  let n := 2 ^ height
  guard (decide (0 < count ∧ count ≤ n))
  let mut swaps : List (Nat × Nat) := []
  let mut out := []
  for i in List.range count do
    -- "QUERY_INDEX"
    let t ← challenge ro [81, 85, 69, 82, 89, 95, 73, 78, 68, 69, 88]
    let key := t.c0.val % (n - i)
    let tail := n - i - 1
    let lookup (j : Nat) := (swaps.lookup j).getD j
    out := lookup key :: out
    swaps := (key, lookup tail) :: swaps
  return out.reverse

structure WhirStage where
  number : Nat
  vars : Nat
  geom : IvcStageGeom
  data : FixedStagePayload
  height : Nat
  nonce : BitVec 256

@[expose] def openStage (ro : RO) (s : WhirStage) (cs : List FoldChallenges) (maskBeta : E) :
    Fs (List (E × E)) := do
  let checkFs (b : Bool) : Fs Unit := fun st => if b then some ((), st) else none
  let liftOpt {α : Type} (o : Option α) : Fs α := fun st => o.map (·, st)
  let n := 2 ^ s.height
  let count := s.geom.queries
  checkFs (decide (0 < count ∧ count ≤ n))
  let mut swaps : List (Nat × Nat) := []
  let mut revIdx := []
  for i in List.range count do
    -- "QUERY_INDEX"
    let t ← challenge ro [81, 85, 69, 82, 89, 95, 73, 78, 68, 69, 88] false
    let key := t.c0.val % (n - i)
    let tail := n - i - 1
    let lookup (j : Nat) := (swaps.lookup j).getD j
    revIdx := lookup key :: revIdx
    swaps := (key, lookup tail) :: swaps
  let indices := revIdx.reverse
  let g := s.geom
  let fibers := NodeWire.chunks g.fiberLen s.data.fiberWords
  let paths := NodeWire.chunks (7 * s.height) s.data.siblingWords
  checkFs (fibers.length == indices.length && paths.length == indices.length)
  let omega := subgroupGenerator (s.height + g.stepVars)
  let mut shifts := []
  for (idx, (fiber,path)) in indices.zip (fibers.zip paths) do
    checkFs (fiberPath ro s.number idx s.nonce fiber (NodeWire.chunks 7 path) == NodeWire.digest s.data.root)
    let mut m := QuinticGoldilocks.zero
    let mut values := []
    if s.number == 0 then
      m ← liftOpt (readExt ((fiber.drop 4).take 5))
      values := (fiber.drop 9).map QuinticGoldilocks.ofBase
    else
      values ← liftOpt (readExts fiber)
    let x := 7 * powMod omega idx goldilocksPrime % goldilocksPrime
    let (y, v) ← liftOpt (foldFiber values x cs)
    shifts := (y, v +ₑ maskBeta *ₑ m) :: shifts
  return shifts.reverse

@[expose] def prepareStages {params : IvcWhirParams} (pi : FixedShapeWhirProof params) : Option (List WhirStage) := do
  let checkOpt (b : Bool) : Option Unit := if b then some () else none
  checkOpt (pi.wellFormed && decide (2 ≤ params.stages.length ∧ params.logCells ≤ 28))
  let mut vars := params.logCells
  let mut result := []
  for ((g,s), i) in (params.stages.zip pi.stages).zipIdx do
    checkOpt (decide (0 < g.stepVars ∧ g.stepVars ≤ 6 ∧ g.stepVars ≤ vars ∧ 0 < g.queries))
    let h := g.frontierSiblings / g.queries
    let arity := 2 ^ g.stepVars
    checkOpt (g.frontierSiblings == h * g.queries && decide (0 < h ∧ vars < h + g.stepVars ∧
      h + g.stepVars ≤ 32 ∧ g.queries ≤ 2 ^ h))
    checkOpt (g.oodLen == (if i == 0 then 5 else 2) &&
      g.fiberLen == (if i == 0 then 9 + arity else 5 * arity))
    result := ⟨i, vars, g, s, h, pi.stage0Nonce⟩ :: result
    vars := vars - g.stepVars
  checkOpt (vars == params.earlyStopVars)
  return result.reverse

/-- Follow a recorded authentication path from the stage-zero root down to a
    leaf. Each parent must have the verifier's canonical input, level and hash. -/
private def recordedChild (log : List (Spec.Bytes × Spec.Bytes)) (idx : Nat) :
    Nat → Spec.Bytes → Option Spec.Bytes
  | 0, digest => some digest
  | level+1, digest => do
    let child ← log.findSome? fun (input,out) => do
      guard (out = digest)
      let [_,_,_,left,right] ← decodeMultiFrameBytes input | none
      guard (left.length = 56 ∧ right.length = 56 ∧ input = fiberParent 0 level left right)
      return if idx.testBit level then right else left
    recordedChild log idx level child

/-- Recover the node's table from the verifier proof and recording alone. Read
    the base values after the four salt and five mask words in each stage-zero
    leaf. Authenticate them under the transmitted nonce and first-stage root. -/
def recoverNodeCoefficients {p : IvcWhirParams} (pi : FixedShapeWhirProof p)
    (log : List (Spec.Bytes × Spec.Bytes)) : Option (List Goldilocks) := do
  let st ← (← prepareStages pi).head?
  let root := NodeWire.digest st.data.root
  let fibers := log.filterMap fun (input,out) => do
    let [_,_,indexBytes,_,payload] ← decodeMultiFrameBytes input | none
    let (i,[]) ← Aggregation.decodeLeb128 indexBytes | none
    guard (i < 2^st.height)
    let ws ← NodeWire.readWords payload
    guard (ws.length = st.geom.fiberLen ∧ input = fiberLeaf 0 i pi.stage0Nonce ws)
    guard (recordedChild log i st.height root = some out)
    return (i,ws.drop 9)
  WhirAssignmentRecovery.decode p.logCells st.height st.geom.stepVars fibers

@[expose] def tensorEval (coeffs : List E) (point : List E) : Option E := do
  let mut terms := coeffs.take (2 ^ point.length)
  for r in point do
    terms ← (NodeWire.chunks 2 terms).mapM fun pair => do
      let [a,b] := pair | none
      return a +ₑ r *ₑ b
  let [v] := terms | none
  return v

@[expose] def checkOpening {p : IvcWhirParams} (ro : RO) (pi : FixedShapeWhirProof p)
    (opening : OpeningClaim) : Fs Unit := do
  let checkFs (b : Bool) : Fs Unit := fun st => if b then some ((), st) else none
  let liftOpt {α : Type} (o : Option α) : Fs α := fun st => o.map (·, st)
  let extsInline (vs : List E) := NodeWire.words (vs.flatMap fun v => [v.c0,v.c1,v.c2,v.c3,v.c4])
  let stages ← liftOpt (prepareStages pi)
  let mut k : Kernel := ⟨opening.value, .one, opening.atPoint, []⟩
  let mut previous : Option (WhirStage × List FoldChallenges) := none
  let mut maskBeta := QuinticGoldilocks.zero
  for s in stages do
    -- "STAGE_ROOT"
    absorb ro [83, 84, 65, 71, 69, 95, 82, 79, 79, 84] (NodeWire.digest s.data.root) false
    let ood ← liftOpt (readExts s.data.oodWords)
    -- "MASK_POINT" / "OOD_POINT"
    let xs ← ood.mapM fun _ => challenge ro (if s.number == 0 then [77, 65, 83, 75, 95, 80, 79, 73, 78, 84] else [79, 79, 68, 95, 80, 79, 73, 78, 84]) false
    -- "MASK_EVAL" / "OOD_EVAL"
    absorb ro (if s.number == 0 then [77, 65, 83, 75, 95, 69, 86, 65, 76] else [79, 79, 68, 95, 69, 86, 65, 76]) (extsInline ood) false
    let mut shifts := []
    if let some (prev, cs) := previous then
      shifts ← openStage ro prev cs maskBeta
      -- "QUERY_VALUES"
      absorb ro [81, 85, 69, 82, 89, 95, 86, 65, 76, 85, 69, 83] (extsInline (shifts.map Prod.snd)) false
    for (x,v) in xs.zip ood do
      -- "MASK_WEIGHT" / "OOD_WEIGHT"
      let w ← challenge ro (if s.number == 0 then [77, 65, 83, 75, 95, 87, 69, 73, 71, 72, 84] else [79, 79, 68, 95, 87, 69, 73, 71, 72, 84]) false
      k := {k with claim := k.claim +ₑ w *ₑ v, points := (w,x) :: k.points}
    if s.number != 0 then
      -- "QUERY_GAMMA"
      let gamma ← challenge ro [81, 85, 69, 82, 89, 95, 71, 65, 77, 77, 65] false
      let mut w := gamma
      for (x,v) in shifts do
        k := {k with claim := k.claim +ₑ w *ₑ v, points := (w,x) :: k.points}
        w := w *ₑ gamma
    let folds ← liftOpt (readExts s.data.foldWords)
    let mut cs := []
    for wire in NodeWire.chunks 5 folds do
      let (next, c) ← foldKernel ro k wire
      k := next
      cs := c :: cs
    if s.number == 0 then
      let m ← liftOpt (readExt pi.maskClaimWords)
      -- "MASK_CLAIM", "MASK_BETA"
      absorb ro [77, 65, 83, 75, 95, 67, 76, 65, 73, 77] (extsInline [m]) false
      maskBeta ← challenge ro [77, 65, 83, 75, 95, 66, 69, 84, 65] false
      checkFs (maskBeta != QuinticGoldilocks.zero)
      k := {k with claim := k.claim +ₑ maskBeta *ₑ m}
    previous := some (s,cs.reverse)
  let some (last, cs) := previous | (fun _ => none)
  let poly ← liftOpt (readExts pi.finalCoeffWords)
  -- "FINAL_POLY"
  absorb ro [70, 73, 78, 65, 76, 95, 80, 79, 76, 89] (extsInline poly) false
  let shifts ← openStage ro last cs maskBeta
  checkFs (shifts.all fun (x,v) => evalCoeffs poly x == v)
  let tensor ← liftOpt (tensorEval poly k.remaining)
  let ptSum := (k.points.map (fun (w,x) => w *ₑ evalCoeffs poly x)).foldl QuinticGoldilocks.add .zero
  checkFs (k.tensorWeight *ₑ tensor +ₑ ptSum == k.claim)

/-- These are the two matrix claims a root verifier must discharge using its compiled public circuits. -/
@[expose] def verifyIvcArgument (profile : AggSigProfile) (cfg : ConcreteIvcConfig) (ro : RO) (d : Nat)
    (stmt : IvcTreeStatement) (pi : FixedShapeWhirProof cfg.params) : Option (MatrixClaim × MatrixClaim) :=
  (do
    let c ← checkR1cs profile cfg ro d stmt pi
    checkOpening ro pi c
    return (c.accumulated, c.matrix) : Fs _).run' {}

end Qsag.MultiDepthQrom.IvcAlgebra

namespace Qsag.MultiDepthQrom
open Qsag IvcAlgebra
abbrev ConcreteIvcConfig := IvcAlgebra.ConcreteIvcConfig

/-- Verify the PCS and close both claims on the verifier-selected numeric matrix coefficients. -/
@[expose] def verifyConcreteIvcStep (profile : AggSigProfile) (cfg : ConcreteIvcConfig)
    (ro : Spec.Bytes → Spec.Bytes) (d : Nat) (stmt : IvcTreeStatement)
    (pi : FixedShapeWhirProof cfg.params) : Bool :=
  decide (stmt.hi = stmt.lo + 2 ^ d ∧ 0 < stmt.totalQuorums) && pi.wellFormed && initialRowSumOk pi &&
  match verifyIvcArgument profile cfg ro d stmt pi with
  | none => false
  | some (old,newClaim) =>
    checkSparseMatrix cfg.params.logCells cfg.matrixEntries old &&
    checkSparseMatrix cfg.params.logCells cfg.matrixEntries newClaim

@[expose] def verifyConcreteIvcRoot (profile : AggSigProfile) (cfg : ConcreteIvcConfig)
    (ro : Spec.Bytes → Spec.Bytes) (d : Nat) (stmt : IvcTreeStatement)
    (pi : FixedShapeWhirProof cfg.params) : Bool :=
  verifyConcreteIvcStep profile cfg ro d stmt pi

theorem verifyConcreteIvcRoot_rejects_interval (profile : AggSigProfile) (cfg : ConcreteIvcConfig)
    (ro : Spec.Bytes → Spec.Bytes) (d : Nat) (stmt : IvcTreeStatement)
    (pi : FixedShapeWhirProof cfg.params) (h : stmt.hi ≠ stmt.lo + 2 ^ d) :
    verifyConcreteIvcRoot profile cfg ro d stmt pi = false := by
  simp [verifyConcreteIvcRoot, verifyConcreteIvcStep, h]

theorem verifyConcreteIvcRoot_rejects_shape (profile : AggSigProfile) (cfg : ConcreteIvcConfig)
    (ro : Spec.Bytes → Spec.Bytes) (d : Nat) (stmt : IvcTreeStatement)
    (pi : FixedShapeWhirProof cfg.params) (h : pi.wellFormed = false) :
    verifyConcreteIvcRoot profile cfg ro d stmt pi = false := by
  simp [verifyConcreteIvcRoot, verifyConcreteIvcStep, h]

theorem verifyConcreteIvcRoot_first_row (profile : AggSigProfile) (cfg : ConcreteIvcConfig)
    (ro : Spec.Bytes → Spec.Bytes) (d : Nat) (stmt : IvcTreeStatement) (pi : FixedShapeWhirProof cfg.params)
    (h : verifyConcreteIvcRoot profile cfg ro d stmt pi = true) : initialRowSumOk pi = true := by
  unfold verifyConcreteIvcRoot verifyConcreteIvcStep at h
  exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).2

theorem tooth_first_row_limb_bitflip (profile : AggSigProfile) (ro : Spec.Bytes → Spec.Bytes)
    (entries : List SparseEntry) :
    ¬ (verifyConcreteIvcRoot profile ⟨limbTestParams,1,1,24,entries⟩ ro 2
      ⟨[],0,0,4,4,[42]⟩ flippedRowProof = true) := by
  intro h
  have hh := verifyConcreteIvcRoot_first_row _ _ _ _ _ _ h
  rw [flippedRowProof_first_round.2.2] at hh
  cases hh

#verify_constructive verifyConcreteIvcRoot_first_row tooth_first_row_limb_bitflip
#tooth_pair verifyConcreteIvcRoot_first_row vs tooth_first_row_limb_bitflip

#verify_constructive verifyConcreteIvcRoot_rejects_interval verifyConcreteIvcRoot_rejects_shape
#verify_kernel verifyConcreteIvcRoot IvcAlgebra.foldMatrixClaims
end Qsag.MultiDepthQrom
end
