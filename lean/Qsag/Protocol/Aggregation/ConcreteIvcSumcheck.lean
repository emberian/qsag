module
public import Qsag.Protocol.Aggregation.ConcreteIvcTranscript
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag.MultiDepthQrom
open Qsag
attribute [-instance] Fin.instLinearOrderPackage
set_option autoImplicit false
abbrev E := QuinticGoldilocks

namespace IvcAlgebra
local infixl:65 " +ₑ " => QuinticGoldilocks.add
local infixl:65 " -ₑ " => QuinticGoldilocks.sub
local infixl:70 " *ₑ " => QuinticGoldilocks.mul

def base (n : Nat) : E := .ofBase (Goldilocks.ofNat n)
def sum (xs : List E) : E := xs.foldl QuinticGoldilocks.add .zero
def dot (x y : List E) : E := sum (x.zipWith QuinticGoldilocks.mul y)
def limbs (v : E) := [v.c0,v.c1,v.c2,v.c3,v.c4]
def exts (v : List E) := NodeWire.words (v.flatMap limbs)

@[expose] def readExt : List Goldilocks → Option E
  | [a,b,c,d,e] => some ⟨a,b,c,d,e⟩
  | _ => none

@[expose] def readExts (w : List Goldilocks) := (NodeWire.chunks 5 w).mapM readExt

@[expose] def evalCoeffs (p : List E) (x : E) : E :=
  p.foldr (fun c acc => c +ₑ x *ₑ acc) .zero

@[expose] def equalityBasis (x y : List E) : E :=
  (x.zipWith (fun a b => (.one -ₑ a) *ₑ (.one -ₑ b) +ₑ a *ₑ b) y).foldl
    QuinticGoldilocks.mul .one

@[expose] def vertexWeight (point : List E) (vertex : Nat) : E :=
  (point.zipIdx.map fun (r, i) => if vertex.testBit i then r else .one -ₑ r).foldl
    QuinticGoldilocks.mul .one

/-- MLE of the indicator of the first k rows, in least-significant-coordinate order. -/
@[expose] def prefixSelector (point : List E) (k : Nat) : E :=
  if k == 2 ^ point.length then .one else
    point.zipIdx.foldl (fun v (r, i) =>
      if k.testBit i then (.one -ₑ r) +ₑ r *ₑ v else (.one -ₑ r) *ₑ v) .zero

abbrev RO := Spec.Bytes → Spec.Bytes
structure FsTrace where
  state : Spec.Bytes := []
  reverseLog : QromQueryTranscript := []

abbrev Fs := StateT FsTrace Option

def askHash (ro : RO) (input : Spec.Bytes) : Fs Spec.Bytes := do
  let out := ro input
  modify fun st => {st with reverseLog := (input,out) :: st.reverseLog}
  return out

@[expose] def absorb (ro : RO) (tag : Spec.Bytes) (payload : Spec.Bytes) (record : Bool := true) : Fs Unit :=
  fun st =>
    -- "IVC-FRAME"
    let input := encodeMultiFrame [[73, 86, 67, 45, 70, 82, 65, 77, 69], st.state, tag, payload]
    let digest := ro input
    if digest.length == 56 then
      some ((), { state := digest, reverseLog := if record then (input, digest) :: st.reverseLog else st.reverseLog })
    else none

@[expose] def challenge (ro : RO) (tag : Spec.Bytes) (record : Bool := true) : Fs E :=
  fun st =>
    -- "IVC-SQUEEZE"
    let input := encodeMultiFrame [[73, 86, 67, 45, 83, 81, 85, 69, 69, 90, 69], st.state, tag]
    let raw := ro input
    if raw.length == 56 then
      match NodeWire.readWords (raw.take 40) with
      | some ws =>
        match readExt ws with
        | some ext =>
          some (ext, { state := raw, reverseLog := if record then (input, raw) :: st.reverseLog else st.reverseLog })
        | none => none
      | none => none
    else none

@[expose] def sumcheck (ro : RO) (roundTag squeezeTag : Spec.Bytes) (vars width : Nat)
    (claim : E) (polys : List (List E)) (record : Bool := true) : Fs (E × List E) := do
  let _ ← (fun st => if polys.length == vars then some ((), st) else none : Fs Unit)
  let mut c := claim
  let mut point := []
  for poly in polys do
    let _ ← (fun st =>
      if poly.length == width && evalCoeffs poly .zero +ₑ evalCoeffs poly .one == c then some ((), st) else none : Fs Unit)
    absorb ro roundTag (NodeWire.words (poly.flatMap fun v => [v.c0,v.c1,v.c2,v.c3,v.c4])) record
    let r ← challenge ro squeezeTag record
    point := r :: point
    c := evalCoeffs poly r
  return (c, point.reverse)

structure MatrixClaim where
  point : List E
  value : E

def MatrixClaim.encode (c : MatrixClaim) := exts (c.point ++ [c.value])

structure R1csArgument where
  acc : MatrixClaim
  row : List (List E)
  a : E
  b : E
  c : E
  col : List (List E)
  matrixEval : E
  zEval : E

def parseArgument (log : Nat) (wire : List Goldilocks) : Option R1csArgument := do
  let xs ← readExts wire
  guard (xs.length == 15 * log + 9)
  let k := 2 * log + 3
  let acc :: rest := xs.drop k | none
  let row := NodeWire.chunks 10 (rest.take (10 * log))
  let a :: b :: c :: rest := rest.drop (10 * log) | none
  let [mat, z] := rest.drop (3 * log) | none
  return ⟨⟨xs.take k, acc⟩, row, a,b,c, NodeWire.chunks 3 (rest.take (3 * log)), mat,z⟩

def publicWeights (lambda : E) (inputs : List E) : List E × E := Id.run do
  let mut w := lambda
  let mut weights := [w]
  let mut claim := w
  for x in inputs do
    w := w *ₑ lambda
    weights := w :: weights
    claim := claim +ₑ w *ₑ x
  return (weights.reverse, claim)

structure SparseEntry where
  row : Nat
  col : Nat
  plane : Fin 3
  step : Bool
  coeff : Goldilocks
  deriving DecidableEq, Repr

structure ConcreteIvcConfig where
  params : IvcWhirParams
  numSboxLeaf : Nat
  numSboxStep : Nat
  publicWidth : Nat
  /-- Public verification key for the arithmetic relation. The matrix compiler determines
      which signature and child-verification constraints this key checks. -/
  matrixEntries : List SparseEntry
  deriving DecidableEq, Repr

def ConcreteIvcConfig.encode (c : ConcreteIvcConfig) : Spec.Bytes :=
  encodeMultiFrame ([c.params.logCells, c.params.earlyStopVars, c.numSboxLeaf, c.numSboxStep, c.publicWidth].map leb128 ++
    c.params.stages.map (fun g => encodeMultiFrame
      ([g.stepVars, g.oodLen, g.queries, g.fiberLen, g.frontierSiblings].map leb128)) ++
    [encodeMultiFrame (c.matrixEntries.map fun e => encodeMultiFrame
      ([e.row,e.col,e.plane.val,if e.step then 1 else 0,e.coeff.val].map leb128))])

structure OpeningClaim where
  accumulated : MatrixClaim
  matrix : MatrixClaim
  atPoint : List E
  value : E

def argumentPublicFrame (stmt : IvcTreeStatement) (accHash : Spec.Bytes) (commitRoot : BitVec 448) :=
  encodeMultiFrame [NodeWire.statement stmt, accHash, encodeNatLeBytes 56 commitRoot.toNat]

def publicCells (frame : Spec.Bytes) :=
  (NodeWire.chunks 7 frame).map (fun c => Goldilocks.ofNat (decodeNatLeBytes c))

def fixedPublicCells (cfg : ConcreteIvcConfig) (frame : Spec.Bytes) : Option (List Goldilocks) := do
  let inputs := publicCells frame
  guard (decide (inputs.length ≤ cfg.publicWidth ∧ cfg.publicWidth < 2 ^ cfg.params.logCells))
  return inputs ++ List.replicate (cfg.publicWidth - inputs.length) Goldilocks.zero

def startArgument (profile : AggSigProfile) (cfg : ConcreteIvcConfig) (ro : RO) (d : Nat)
    (stmt : IvcTreeStatement) (acc : MatrixClaim) (nonce : BitVec 256) (commitRoot : BitVec 448)
    (root : Poseidon2Gl24.Digest7) : Fs (List E) := do
  -- "IVC-MATRIX-POINT"
  let accHash ← askHash ro (encodeMultiFrame [[73, 86, 67, 45, 77, 65, 84, 82, 73, 88, 45, 80, 79, 73, 78, 84], acc.encode])
  guard (accHash.length == 56)
  let publicFrame := argumentPublicFrame stmt accHash commitRoot
  let inputs ← liftM (m := Option) (fixedPublicCells cfg publicFrame)
  -- "IVC-R1CS-v1"
  absorb ro [73, 86, 67, 45, 82, 49, 67, 83, 45, 118, 49] (encodeMultiFrame [cfg.encode, leb128 d,
    [if profile == .xmssPoseidon2 then 1 else 2], publicFrame,
    encodeNatLeBytes 32 nonce.toNat, NodeWire.digest root])
  return inputs.map QuinticGoldilocks.ofBase

/-- The R1CS verifier returns two fixed-matrix obligations and one polynomial opening. -/
@[expose] def checkR1cs (profile : AggSigProfile) (cfg : ConcreteIvcConfig) (ro : RO) (d : Nat)
    (stmt : IvcTreeStatement) (pi : FixedShapeWhirProof cfg.params) : Fs OpeningClaim := do
  let checkFs (b : Bool) : Fs Unit := fun st => if b then some ((), st) else none
  let liftOpt {α : Type} (o : Option α) : Fs α := fun st => o.map (·, st)
  let extsInline (vs : List E) := NodeWire.words (vs.flatMap fun v => [v.c0,v.c1,v.c2,v.c3,v.c4])
  let sumInline (xs : List E) : E := xs.foldl QuinticGoldilocks.add .zero
  let dotInline (x y : List E) : E := sumInline (x.zipWith QuinticGoldilocks.mul y)
  let log := cfg.params.logCells
  let n := 2 ^ log
  checkFs (pi.wellFormed && stmt.hi == stmt.lo + 2 ^ d && decide (0 < stmt.totalQuorums))
  checkFs (decide (cfg.numSboxLeaf ≤ n ∧ cfg.numSboxStep ≤ n))
  let p ← liftOpt (do
    let xs ← readExts pi.algebraWords
    let _ ← if xs.length == 15 * log + 9 then some () else none
    let k := 2 * log + 3
    let acc :: rest := xs.drop k | none
    let row := NodeWire.chunks 10 (rest.take (10 * log))
    let a :: b :: c :: rest := rest.drop (10 * log) | none
    let [mat, z] := rest.drop (3 * log) | none
    return (⟨⟨xs.take k, acc⟩, row, a, b, c, NodeWire.chunks 3 (rest.take (3 * log)), mat, z⟩ : R1csArgument))
  let stage ← liftOpt pi.stages.head?
  -- "IVC-MATRIX-POINT"
  let accIn := encodeMultiFrame [[73, 86, 67, 45, 77, 65, 84, 82, 73, 88, 45, 80, 79, 73, 78, 84], extsInline (p.acc.point ++ [p.acc.value])]
  let accHash := ro accIn
  checkFs (accHash.length == 56)
  let publicFrame := encodeMultiFrame [NodeWire.statement stmt, accHash, encodeNatLeBytes 56 pi.witnessCommitRoot.toNat]
  let rawPub := (NodeWire.chunks 7 publicFrame).map (fun c => Goldilocks.ofNat (decodeNatLeBytes c))
  checkFs (decide (rawPub.length ≤ cfg.publicWidth ∧ cfg.publicWidth < 2 ^ log))
  let inputs := (rawPub ++ List.replicate (cfg.publicWidth - rawPub.length) Goldilocks.zero).map QuinticGoldilocks.ofBase
  let cfgEnc := encodeMultiFrame ([cfg.params.logCells, cfg.params.earlyStopVars, cfg.numSboxLeaf, cfg.numSboxStep, cfg.publicWidth].map leb128 ++
    cfg.params.stages.map (fun g => encodeMultiFrame
      ([g.stepVars, g.oodLen, g.queries, g.fiberLen, g.frontierSiblings].map leb128)) ++
    [encodeMultiFrame (cfg.matrixEntries.map fun e => encodeMultiFrame
      ([e.row, e.col, e.plane.val, if e.step then 1 else 0, e.coeff.val].map leb128))])
  -- "IVC-R1CS-v1"
  absorb ro [73, 86, 67, 45, 82, 49, 67, 83, 45, 118, 49] (encodeMultiFrame [cfgEnc, leb128 d,
    [if profile == .xmssPoseidon2 then 1 else 2], publicFrame,
    encodeNatLeBytes 32 pi.stage0Nonce.toNat, NodeWire.digest stage.root]) false
  -- "TAU"
  let tau ← (List.range log).mapM (fun _ => challenge ro [84, 65, 85] false)
  -- "ROW_ROUND", "rx"
  let (rowLast, rx) ← sumcheck ro [82, 79, 87, 95, 82, 79, 85, 78, 68] [114, 120] log 10 .zero p.row false
  let ab := p.a *ₑ p.b
  let a2 := p.a *ₑ p.a
  let a7 := a2 *ₑ a2 *ₑ a2 *ₑ p.a
  let sel := prefixSelector rx (if d == 0 then cfg.numSboxLeaf else cfg.numSboxStep)
  checkFs (equalityBasis tau rx *ₑ (sel *ₑ (a7 -ₑ ab) +ₑ ab -ₑ p.c) == rowLast)
  -- "ROW_VALUES"
  absorb ro [82, 79, 87, 95, 86, 65, 76, 85, 69, 83] (extsInline [p.a, p.b, p.c]) false
  -- "SELECT_A", "SELECT_B", "PUBLIC_BATCH"
  let u ← challenge ro [83, 69, 76, 69, 67, 84, 95, 65] false
  let v ← challenge ro [83, 69, 76, 69, 67, 84, 95, 66] false
  let lambda ← challenge ro [80, 85, 66, 76, 73, 67, 95, 66, 65, 84, 67, 72] false
  let (weights, pub) := Id.run do
    let mut w := lambda
    let mut ws := [w]
    let mut cl := w
    for x in inputs do
      w := w *ₑ lambda
      ws := w :: ws
      cl := cl +ₑ w *ₑ x
    return (ws.reverse, cl)
  let mix := [.one -ₑ u, u, .one -ₑ u].zipWith QuinticGoldilocks.mul [.one -ₑ v, .one -ₑ v, v]
  -- "COL_ROUND", "ry"
  let (colLast, ry) ← sumcheck ro [67, 79, 76, 95, 82, 79, 85, 78, 68] [114, 121] log 3 (pub +ₑ dotInline mix [p.a, p.b, p.c]) p.col false
  let publicCol := sumInline (weights.zipIdx.map fun (w, i) => w *ₑ vertexWeight ry i)
  checkFs ((p.matrixEval +ₑ publicCol) *ₑ p.zEval == colLast)
  -- "TERMINAL"
  absorb ro [84, 69, 82, 77, 73, 78, 65, 76] (extsInline [p.matrixEval, p.zEval]) false
  let kindVal : E := .ofBase (Goldilocks.ofNat (if d == 0 then 0 else 1))
  return ⟨p.acc, ⟨rx ++ ry ++ [u, v, kindVal], p.matrixEval⟩, ry, p.zEval⟩

/-- Fold the two old and two new child claims; the output still needs a public matrix evaluation. -/
def foldMatrixClaims (ro : RO) (log : Nat) (claims : List MatrixClaim)
    (rounds : List (List E)) (answer : E) : Fs MatrixClaim := do
  let dim := 2 * log + 3
  guard (claims.length == 4 && claims.all (fun c => c.point.length == dim))
  -- "IVC-MAT-BATCH"
  for c in claims do absorb ro [73, 86, 67, 45, 77, 65, 84, 45, 66, 65, 84, 67, 72] c.encode
  -- "BATCH_WEIGHT"
  let beta ← challenge ro [66, 65, 84, 67, 72, 95, 87, 69, 73, 71, 72, 84]
  let weights := [QuinticGoldilocks.one, beta, beta *ₑ beta, beta *ₑ beta *ₑ beta]
  -- "MAT_ROUND", "MAT_POINT"
  let (last, pt) ← sumcheck ro [77, 65, 84, 95, 82, 79, 85, 78, 68] [77, 65, 84, 95, 80, 79, 73, 78, 84] dim 3
    (dot weights (claims.map MatrixClaim.value)) rounds
  guard (dot weights (claims.map fun c => equalityBasis pt c.point) *ₑ answer == last)
  return ⟨pt, answer⟩

/-- Evaluate the two public sparse shapes at the complete accumulated point. -/
@[expose] def checkSparseMatrix (log : Nat) (entries : List SparseEntry) (c : MatrixClaim) : Bool := Id.run do
  let [u,v,kind] := c.point.drop (2 * log) | return false
  let rx := c.point.take log
  let ry := (c.point.drop log).take log
  let p0 := (.one -ₑ u) *ₑ (.one -ₑ v)
  let p1 := u *ₑ (.one -ₑ v)
  let p2 := (.one -ₑ u) *ₑ v
  let mut acc := QuinticGoldilocks.zero
  for e in entries do
    if e.row ≥ 2 ^ log || e.col ≥ 2 ^ log then return false
    let pl := match e.plane.val with | 0 => p0 | 1 => p1 | _ => p2
    acc := acc +ₑ .ofBase e.coeff *ₑ vertexWeight rx e.row *ₑ vertexWeight ry e.col
      *ₑ pl *ₑ (if e.step then kind else .one -ₑ kind)
  return acc == c.value

def childMatrixClaims (profile : AggSigProfile) (cfg : ConcreteIvcConfig) (ro : RO)
    (d : Nat) (l r : IvcTreeStatement) (pl pr : FixedShapeWhirProof cfg.params) :
    Option (List MatrixClaim) := do
  let a ← (checkR1cs profile cfg ro d l pl).run' {}
  let b ← (checkR1cs profile cfg ro d r pr).run' {}
  return [a.accumulated,a.matrix,b.accumulated,b.matrix]

@[expose] def parentFoldAgrees (profile : AggSigProfile) (cfg : ConcreteIvcConfig) (ro : RO)
    (d : Nat) (l r : IvcTreeStatement) (pl pr parent : FixedShapeWhirProof cfg.params)
    (wire : List Goldilocks) : Bool := (do
  let checkFs (b : Bool) : Fs Unit := fun st => if b then some ((), st) else none
  let extsInline (vs : List E) := NodeWire.words (vs.flatMap fun v => [v.c0,v.c1,v.c2,v.c3,v.c4])
  let dotInline (x y : List E) : E := (x.zipWith QuinticGoldilocks.mul y).foldl QuinticGoldilocks.add .zero
  let log := cfg.params.logCells
  let ca ← (checkR1cs profile cfg ro d l pl).run' {}
  let cb ← (checkR1cs profile cfg ro d r pr).run' {}
  let claims := [ca.accumulated, ca.matrix, cb.accumulated, cb.matrix]
  let xs ← readExts wire
  let dim := 2 * log + 3
  let n := 3 * dim
  let [answer] := xs.drop n | none
  let rounds := NodeWire.chunks 3 (xs.take n)
  let folded ← (do
    checkFs (claims.length == 4 && claims.all (fun c => c.point.length == dim))
    -- "IVC-MAT-BATCH"
    for c in claims do absorb ro [73, 86, 67, 45, 77, 65, 84, 45, 66, 65, 84, 67, 72] (extsInline (c.point ++ [c.value])) false
    -- "BATCH_WEIGHT"
    let beta ← challenge ro [66, 65, 84, 67, 72, 95, 87, 69, 73, 71, 72, 84] false
    let weights := [QuinticGoldilocks.one, beta, beta *ₑ beta, beta *ₑ beta *ₑ beta]
    -- "MAT_ROUND", "MAT_POINT"
    let (last, pt) ← sumcheck ro [77, 65, 84, 95, 82, 79, 85, 78, 68] [77, 65, 84, 95, 80, 79, 73, 78, 84] dim 3
      (dotInline weights (claims.map MatrixClaim.value)) rounds false
    checkFs (dotInline weights (claims.map fun c => equalityBasis pt c.point) *ₑ answer == last)
    return (⟨pt, answer⟩ : MatrixClaim) : Fs MatrixClaim).run' {}
  let pxs ← readExts parent.algebraWords
  let _ ← if pxs.length == 15 * log + 9 then some () else none
  let accVal :: _ := pxs.drop dim | none
  if folded.point == pxs.take dim && folded.value == accVal then some () else none : Option Unit).isSome

end IvcAlgebra
end Qsag.MultiDepthQrom
end
