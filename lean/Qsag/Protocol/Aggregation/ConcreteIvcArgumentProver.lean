module
public import Qsag.Protocol.Aggregation.ConcreteIvcOpeningProver
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag.MultiDepthQrom.IvcAlgebra
open Qsag
set_option autoImplicit false
attribute [-instance] Fin.instLinearOrderPackage
local infixl:65 " +ₑ " => QuinticGoldilocks.add
local infixl:65 " -ₑ " => QuinticGoldilocks.sub
local infixl:70 " *ₑ " => QuinticGoldilocks.mul

/-- Newton interpolation from p(0), ..., p(k), in the power basis used on the wire. -/
def interpolate (samples : List E) : List E := Id.run do
  let mut diffs := samples
  let mut basis := [QuinticGoldilocks.one]
  let mut coeffs := Array.replicate samples.length QuinticGoldilocks.zero
  for i in [:samples.length] do
    let delta := diffs.head!
    for (c,j) in basis.zipIdx do coeffs := coeffs.modify j (fun a => a +ₑ c *ₑ delta)
    diffs := diffs.tail.zipWith QuinticGoldilocks.sub diffs
    let inv := base (powMod (i+1) (goldilocksPrime-2) goldilocksPrime)
    basis := (List.range (basis.length+1)).map fun j =>
      ((if j == 0 then .zero else (basis[j-1]?).getD .zero) -ₑ base i *ₑ (basis[j]?).getD .zero) *ₑ inv
  return coeffs.toList

def lerp (a b t : E) := a +ₑ t *ₑ (b -ₑ a)

inductive RoundKind where | row | col

def roundValue (kind : RoundKind) (vs : Array E) : E :=
  match kind with
  | .row =>
    let a := vs[0]!
    let ab := a *ₑ vs[1]!
    let aa := a *ₑ a
    vs[4]! *ₑ (vs[3]! *ₑ (aa *ₑ aa *ₑ aa *ₑ a -ₑ ab) +ₑ ab -ₑ vs[2]!)
  | .col => vs[0]! *ₑ vs[1]!

def proveRounds (ro : RO) (kind : RoundKind) (log : Nat) (tables : Array (Array E)) :
    Fs (List (List E) × List E × Array E) := do
  let (width, label, squeezeTag) : Nat × Spec.Bytes × Spec.Bytes := match kind with
    | .row => (10, [82, 79, 87, 95, 82, 79, 85, 78, 68], [114, 120])
    | .col => (3, [67, 79, 76, 95, 82, 79, 85, 78, 68], [114, 121])
  let mut tabs := tables
  let mut rounds := []
  let mut coords := []
  for _ in [:log] do
    let half := tabs[0]!.size / 2
    let samples := (List.range width).map fun t => Id.run do
      let mut total := QuinticGoldilocks.zero
      for j in [:half] do
        total := total +ₑ roundValue kind (tabs.map fun arr => lerp arr[2*j]! arr[2*j+1]! (base t))
      return total
    let co := interpolate samples
    absorb ro label (exts co)
    let r ← challenge ro squeezeTag
    rounds := co :: rounds
    coords := r :: coords
    tabs := tabs.map fun arr => (Array.range half).map fun j => lerp arr[2*j]! arr[2*j+1]! r
  return (rounds.reverse,coords.reverse,tabs.map (fun arr => arr[0]!))

def R1csArgument.encode (p : R1csArgument) : List Goldilocks :=
  (p.acc.point ++ [p.acc.value] ++ p.row.flatten ++ [p.a,p.b,p.c] ++ p.col.flatten ++
    [p.matrixEval,p.zEval]).flatMap limbs

/-- Prove satisfiability of the verifier's numeric matrices for the supplied private cells.
The prover computes all public cells and verifies every row before committing its assignment. -/
def proveR1csArgument (profile : AggSigProfile) (cfg : ConcreteIvcConfig) (ro : RO)
    (d : Nat) (stmt : IvcTreeStatement) (commitRoot : BitVec 448) (acc : MatrixClaim)
    (seed : Spec.Bytes) (privateCells : List Goldilocks) : Fs (FixedShapeWhirProof cfg.params) := do
  let p := cfg.params
  let log := p.logCells
  let n := 2 ^ log
  guard (stmt.hi == stmt.lo + 2 ^ d && decide (0 < stmt.totalQuorums ∧ log ≤ 28))
  guard (acc.point.length == 2 * log + 3 && checkSparseMatrix log cfg.matrixEntries acc)
  -- "IVC-MATRIX-POINT"
  let hash ← askHash ro (encodeMultiFrame [[73, 86, 67, 45, 77, 65, 84, 82, 73, 88, 45, 80, 79, 73, 78, 84], acc.encode])
  guard (hash.length == 56)
  let inputs ← liftM (m := Option) (fixedPublicCells cfg (argumentPublicFrame stmt hash commitRoot))
  let cells := Goldilocks.one :: inputs ++ privateCells
  guard (decide (cells.length ≤ n))
  let z := (cells ++ List.replicate (n - cells.length) Goldilocks.zero).toArray
  let table := z.map QuinticGoldilocks.ofBase
  let mut abc := Array.replicate 3 (Array.replicate n QuinticGoldilocks.zero)
  for entry in cfg.matrixEntries do
    guard (decide (entry.row < n ∧ entry.col < n))
    if entry.step == (d != 0) then
      abc := abc.modify entry.plane.val (fun r => r.modify entry.row
        (fun a => a +ₑ .ofBase entry.coeff *ₑ table[entry.col]!))
  let sbox := if d == 0 then cfg.numSboxLeaf else cfg.numSboxStep
  guard (decide (sbox ≤ n))
  for i in [:n] do
    let a := abc[0]![i]!
    let aa := a *ₑ a
    guard ((if i < sbox then aa *ₑ aa *ₑ aa *ₑ a else a *ₑ abc[1]![i]!) == abc[2]![i]!)
  -- "IVC-PROVER-NONCE"
  let nonceHash ← askHash ro (encodeMultiFrame [[73, 86, 67, 45, 80, 82, 79, 86, 69, 82, 45, 78, 79, 78, 67, 69], seed])
  guard (nonceHash.length == 56)
  let nonce := BitVec.ofNat 256 (decodeNatLeBytes (nonceHash.take 32))
  let cm ← commitTable ro p seed nonce z
  let _ ← startArgument profile cfg ro d stmt acc nonce commitRoot cm.stage0.stage.data.root
  let tau ← (List.range log).mapM fun _ => challenge ro [84, 65, 85]
  let selectors := (Array.range n).map (fun i => base (if i < sbox then 1 else 0))
  let (rows,rx,answers) ← proveRounds ro .row log
    ((abc.push selectors).push ((Array.range n).map (vertexWeight tau)))
  let a := answers[0]!
  let b := answers[1]!
  let c := answers[2]!
  absorb ro [82, 79, 87, 95, 86, 65, 76, 85, 69, 83] (exts [a,b,c])
  let u ← challenge ro [83, 69, 76, 69, 67, 84, 95, 65]
  let v ← challenge ro [83, 69, 76, 69, 67, 84, 95, 66]
  let lambda ← challenge ro [80, 85, 66, 76, 73, 67, 95, 66, 65, 84, 67, 72]
  let mix := #[(.one -ₑ u) *ₑ (.one -ₑ v), u *ₑ (.one -ₑ v), (.one -ₑ u) *ₑ v]
  let (weights,_) := publicWeights lambda (inputs.map QuinticGoldilocks.ofBase)
  let mut cols := (weights ++ List.replicate (n-weights.length) QuinticGoldilocks.zero).toArray
  for e in cfg.matrixEntries do
    if e.step == (d != 0) then
      cols := cols.modify e.col (fun m => m +ₑ vertexWeight rx e.row *ₑ mix[e.plane.val]! *ₑ .ofBase e.coeff)
  let (col,ry,terminal) ← proveRounds ro .col log #[cols,table]
  let mat := terminal[0]! -ₑ sum (weights.zipIdx.map fun (w,j) => w *ₑ vertexWeight ry j)
  let zEval := terminal[1]!
  absorb ro [84, 69, 82, 77, 73, 78, 65, 76] (exts [mat,zEval])
  let (stages,mask,final) ← proveOpening ro p seed nonce cm ry zEval
  let arg := R1csArgument.mk acc rows a b c col mat zEval
  let pi : FixedShapeWhirProof p := ⟨nonce,commitRoot,arg.encode,stages,mask,final⟩
  guard pi.wellFormed
  return pi

/-- Commit the canonical application witness before constructing an arithmetic argument.
A circuit-specific witness generator supplies the private assignment cells. -/
def proveCommittedIvcArgument {n : Nat} (profile : AggSigProfile) (cfg : ConcreteIvcConfig)
    (ro : RO) (d : Nat) (stmt : IvcTreeStatement) (w : CommittedIvcNodeWitness cfg.params n)
    (acc : MatrixClaim) (seed : Spec.Bytes) (privateCells : List Goldilocks) :
    Fs (FixedShapeWhirProof cfg.params) := do
  -- "IVC-PROVER-NONCE"
  let nonceHash ← askHash ro (encodeMultiFrame [[73, 86, 67, 45, 80, 82, 79, 86, 69, 82, 45, 78, 79, 78, 67, 69], seed])
  guard (nonceHash.length == 56)
  let nonce := BitVec.ofNat 256 (decodeNatLeBytes (nonceHash.take 32))
  let out ← askHash ro (nodeCommitmentInput profile d stmt nonce (NodeWire.node w))
  guard (out.length == 56)
  proveR1csArgument profile cfg ro d stmt (BitVec.ofNat 448 (decodeNatLeBytes out)) acc seed privateCells

def sparseIndex (log : Nat) (e : SparseEntry) :=
  e.row + (e.col + (e.plane.val + (if e.step then 4 else 0)) * 2 ^ log) * 2 ^ log

/-- Sum out the unassigned Boolean suffix using the support of the sparse matrix. -/
def matrixPartialSum (log : Nat) (entries : List SparseEntry) (claims : List MatrixClaim)
    (weights fixed : List E) : E :=
  sum (entries.map fun e =>
    let j := sparseIndex log e
    let factors := claims.map fun c =>
      equalityBasis fixed (c.point.take fixed.length) *ₑ
        vertexWeight (c.point.drop fixed.length) (j / 2 ^ fixed.length)
    .ofBase e.coeff *ₑ vertexWeight fixed j *ₑ dot weights factors)

def proveMatrixFold (ro : RO) (cfg : ConcreteIvcConfig) (claims : List MatrixClaim) :
    Fs (List (List E) × MatrixClaim) := do
  let log := cfg.params.logCells
  let dim := 2 * log + 3
  guard (claims.length == 4 && claims.all (checkSparseMatrix log cfg.matrixEntries))
  for c in claims do absorb ro [73, 86, 67, 45, 77, 65, 84, 45, 66, 65, 84, 67, 72] c.encode
  let beta ← challenge ro [66, 65, 84, 67, 72, 95, 87, 69, 73, 71, 72, 84]
  let weights := [QuinticGoldilocks.one,beta,beta *ₑ beta,beta *ₑ beta *ₑ beta]
  let mut point := []
  let mut rounds := []
  for _ in [:dim] do
    let poly := interpolate ((List.range 3).map fun t =>
      matrixPartialSum log cfg.matrixEntries claims weights (point ++ [base t]))
    absorb ro [77, 65, 84, 95, 82, 79, 85, 78, 68] (exts poly)
    point := point ++ [← challenge ro [77, 65, 84, 95, 80, 79, 73, 78, 84]]
    rounds := poly :: rounds
  let ans := sum (cfg.matrixEntries.map fun e => .ofBase e.coeff *ₑ vertexWeight point (sparseIndex log e))
  return (rounds.reverse,⟨point,ans⟩)

/-- Prepare the parent commitment payload and the public accumulator from both child arguments. -/
def prepareParentWitness (n : Nat) (profile : AggSigProfile) (cfg : ConcreteIvcConfig) (ro : RO)
    (d : Nat) (l r : IvcTreeStatement) (pl pr : FixedShapeWhirProof cfg.params) :
    Option (CommittedIvcNodeWitness cfg.params n × MatrixClaim) := do
  let (a,b) ← verifyIvcArgument profile cfg ro d l pl
  let (c,e) ← verifyIvcArgument profile cfg ro d r pr
  let (rounds,acc) ← (proveMatrixFold ro cfg [a,b,c,e]).run' {}
  return (.parent l r pl pr ((rounds.flatten ++ [acc.value]).flatMap limbs), acc)

#verify_kernel proveR1csArgument proveCommittedIvcArgument proveMatrixFold prepareParentWitness

end Qsag.MultiDepthQrom.IvcAlgebra
end
