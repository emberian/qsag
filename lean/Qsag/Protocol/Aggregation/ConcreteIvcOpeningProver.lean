module
public import Qsag.Protocol.Aggregation.ConcreteIvcWhir

public section
namespace Qsag.MultiDepthQrom.IvcAlgebra
open Qsag
set_option autoImplicit false
attribute [-instance] Fin.instLinearOrderPackage
local infixl:65 " +ₑ " => QuinticGoldilocks.add
local infixl:65 " -ₑ " => QuinticGoldilocks.sub
local infixl:70 " *ₑ " => QuinticGoldilocks.mul

def fieldPower (a : E) : Nat → E
  | 0 => .one
  | n + 1 =>
    let half := fieldPower (a *ₑ a) ((n + 1) / 2)
    if (n + 1) % 2 == 0 then half else a *ₑ half
termination_by n => n

def kernelCoeff (k : Kernel) (i : Nat) : E := Id.run do
  let mut tensor := k.tensorWeight
  if i ≥ 2 ^ k.remaining.length then tensor := .zero
  else
    for (r, j) in k.remaining.zipIdx do
      if i.testBit j then tensor := tensor *ₑ r
  return tensor +ₑ sum (k.points.map fun (w,x) => w *ₑ fieldPower x i)

def proveFold (ro : RO) (k : Kernel) (poly : Array E) :
    Fs (Array E × Kernel × FoldChallenges × List E) := do
  let n := (poly.size + 1) / 2
  let atP (i : Nat) := poly[i]?.getD .zero
  let coeffs := (Array.range (2 * n + 2)).map (kernelCoeff k)
  let atK (i : Nat) := coeffs[i]?.getD .zero
  let mut se := QuinticGoldilocks.zero
  let mut t01 := QuinticGoldilocks.zero
  let mut t10 := QuinticGoldilocks.zero
  for i in [:n] do
    se := se +ₑ atP (2*i) *ₑ atK (2*i)
    t01 := t01 +ₑ atP (2*i) *ₑ atK (2*i+1)
    t10 := t10 +ₑ atP (2*i+1) *ₑ atK (2*i)
  let phi ← beginFold ro se t01 t10
  let mut cf := QuinticGoldilocks.zero
  let mut cg := QuinticGoldilocks.zero
  for i in [:n] do
    let t := atK (2*i+2) +ₑ phi *ₑ atK (2*i+3)
    cf := cf +ₑ atP (2*i) *ₑ t
    cg := cg +ₑ atP (2*i+1) *ₑ t
  let (next,c) ← finishFold ro k se t01 t10 cf cg phi
  let h (j : Nat) := atP (2*j) +ₑ c.theta *ₑ atP (2*j+1)
  let out := (Array.range (n+1)).map fun j =>
    atP (2*j+1) +ₑ c.alpha *ₑ h j +ₑ (if j == 0 then .zero else c.beta *ₑ h (j-1))
  return (out,next,c,[se,t01,t10,cf,cg])

def digestOfBytes (bs : Spec.Bytes) : Option Poseidon2Gl24.Digest7 := do
  let [a,b,c,d,e,f,g] ← NodeWire.readWords bs | none
  return ⟨a,b,c,d,e,f,g⟩

structure CommittedStage where
  stage : WhirStage
  fibers : Array (List Goldilocks)
  levels : Array (Array Spec.Bytes)

def freshWords (ro : RO) (seed : Spec.Bytes) (tag : Spec.Bytes) (index count : Nat) :
    Fs (List Goldilocks) := do
  -- "IVC-PROVER-COINS"
  let raw ← askHash ro (encodeMultiFrame [[73, 86, 67, 45, 80, 82, 79, 86, 69, 82, 45, 67, 79, 73, 78, 83], seed,
    tag, leb128 index])
  guard (raw.length == 56 && decide (count ≤ 7))
  liftM (m := Option) (NodeWire.readWords (raw.take (count*8)))

/-- Reference encoder, using direct polynomial evaluation on the shifted two-adic domain. -/
def commitStage (ro : RO) (seed : Spec.Bytes) (i vars : Nat) (g : IvcStageGeom)
    (nonce : BitVec 256) (poly mask : List E) : Fs CommittedStage := do
  guard (decide (0 < g.queries ∧ 0 < g.stepVars ∧ g.stepVars ≤ 6 ∧ g.stepVars ≤ vars))
  let height := g.frontierSiblings / g.queries
  let log := height + g.stepVars
  guard (decide (vars < log ∧ log ≤ 32) && height * g.queries == g.frontierSiblings)
  let leaves := 2 ^ height
  let arity := 2 ^ g.stepVars
  let omega := subgroupGenerator log
  let zeta := subgroupGenerator g.stepVars
  let mut fibers := #[]
  let mut hashes := #[]
  for j in [:leaves] do
    let x := 7 * powMod omega j goldilocksPrime % goldilocksPrime
    let mut xi := x
    let mut fiber := []
    if i == 0 then
      -- "LEAF-SALT"
      let salt ← freshWords ro seed [76, 69, 65, 70, 45, 83, 65, 76, 84] j 4
      fiber := salt ++ limbs (evalCoeffs mask (base (powMod x arity goldilocksPrime)))
    let mut vals := []
    for _ in [:arity] do
      let v := evalCoeffs poly (base xi)
      vals := (if i == 0 then [v.c0] else limbs v) :: vals
      xi := xi * zeta % goldilocksPrime
    fiber := fiber ++ vals.reverse.flatten
    guard (fiber.length == g.fiberLen)
    fibers := fibers.push fiber
    hashes := hashes.push (← askHash ro (fiberLeaf i j nonce fiber))
  let mut levels := #[hashes]
  for level in [:height] do
    let mut parents := #[]
    for j in [:hashes.size / 2] do
      parents := parents.push (← askHash ro (fiberParent i level hashes[2*j]! hashes[2*j+1]!))
    levels := levels.push parents
    hashes := parents
  let root ← liftM (m := Option) (digestOfBytes hashes[0]!)
  return ⟨⟨i,vars,g,⟨root,[],[],[],[]⟩,height,nonce⟩, fibers, levels⟩

def revealStage (ro : RO) (cm : CommittedStage) (cs : List FoldChallenges) (beta : E) :
    Fs (FixedStagePayload × List (E × E)) := do
  let s := cm.stage
  let idx ← queryIndices ro s.height s.geom.queries
  let mut paths := []
  let mut shifts := []
  let omega := subgroupGenerator (s.height + s.geom.stepVars)
  for j in idx do
    let mut k := j
    let mut path := []
    for level in [:s.height] do
      let sibling := cm.levels[level]![(k ^^^ 1)]!
      path := (← liftM (m := Option) (NodeWire.readWords sibling)) :: path
      k := k / 2
    paths := path.reverse.flatten :: paths
    let ws := cm.fibers[j]!
    let x := 7 * powMod omega j goldilocksPrime % goldilocksPrime
    let (mask, values) ← liftM (m := Option) (do
      if s.number == 0 then
        return (← readExt ((ws.drop 4).take 5), (ws.drop 9).map QuinticGoldilocks.ofBase)
      return (QuinticGoldilocks.zero, ← readExts ws))
    let (y,v) ← liftM (m := Option) (foldFiber values x cs)
    shifts := (y, v +ₑ beta *ₑ mask) :: shifts
  let data := {s.data with
    fiberWords := idx.flatMap (fun j => cm.fibers[j]!)
    siblingWords := paths.reverse.flatten}
  return (data, shifts.reverse)

structure TableCommitment where
  stage0 : CommittedStage
  coeffs : List E
  mask : List E

def monomialCoeffs (log : Nat) (table : Array Goldilocks) : Array E := Id.run do
  let mut arr := table.map QuinticGoldilocks.ofBase
  for j in [:log] do
    for i in [:arr.size] do
      if i.testBit j then
        arr := arr.set! i (arr[i]! -ₑ arr[i - 2 ^ j]!)
  return arr

def commitTable (ro : RO) (p : IvcWhirParams) (seed : Spec.Bytes) (nonce : BitVec 256)
    (table : Array Goldilocks) : Fs TableCommitment := do
  guard (table.size == 2 ^ p.logCells)
  let g :: _ := p.stages | failure
  let mask ← (List.range (2 ^ (p.logCells - g.stepVars) + 2)).mapM
    -- "MASK"
    (fun i => do liftM (m := Option) (readExt (← freshWords ro seed [77, 65, 83, 75] i 5)))
  let coeffs := (monomialCoeffs p.logCells table).toList
  return ⟨← commitStage ro seed 0 p.logCells g nonce coeffs mask, coeffs, mask⟩

def proveOpening (ro : RO) (p : IvcWhirParams) (seed : Spec.Bytes) (nonce : BitVec 256)
    (cm : TableCommitment) (point : List E) (value : E) :
    Fs (List FixedStagePayload × List Goldilocks × List Goldilocks) := do
  guard (point.length == p.logCells && decide (2 ≤ p.stages.length))
  let mut k := Kernel.mk value .one point []
  let mut poly := cm.coeffs.toArray
  let mut maskClaim := QuinticGoldilocks.zero
  let mut beta := QuinticGoldilocks.zero
  let mut prev : Option (CommittedStage × List FoldChallenges) := none
  let mut stages := []
  for (g,i) in p.stages.zipIdx do
    let c ← if i == 0 then pure cm.stage0 else
      commitStage ro seed i k.remaining.length g nonce poly.toList []
    -- "STAGE_ROOT"
    absorb ro [83, 84, 65, 71, 69, 95, 82, 79, 79, 84] (NodeWire.digest c.stage.data.root)
    let xs ← (List.range g.oodLen).mapM fun _ =>
      challenge ro (if i == 0 then [77, 65, 83, 75, 95, 80, 79, 73, 78, 84] else [79, 79, 68, 95, 80, 79, 73, 78, 84])
    let ood := xs.map (evalCoeffs poly.toList)
    absorb ro (if i == 0 then [77, 65, 83, 75, 95, 69, 86, 65, 76] else [79, 79, 68, 95, 69, 86, 65, 76]) (exts ood)
    let mut shifted := []
    if let some (previous, f) := prev then
      let (payload, shifts) ← revealStage ro previous f beta
      stages := payload :: stages
      shifted := shifts
      absorb ro [81, 85, 69, 82, 89, 95, 86, 65, 76, 85, 69, 83] (exts (shifted.map Prod.snd))
    for (x,v) in xs.zip ood do
      let w ← challenge ro (if i == 0 then [77, 65, 83, 75, 95, 87, 69, 73, 71, 72, 84] else [79, 79, 68, 95, 87, 69, 73, 71, 72, 84])
      k := {k with points := (w,x) :: k.points, claim := k.claim +ₑ w *ₑ v}
    if i != 0 then
      let gamma ← challenge ro [81, 85, 69, 82, 89, 95, 71, 65, 77, 77, 65]
      let mut w := gamma
      for (x,v) in shifted do
        k := {k with points := (w,x) :: k.points, claim := k.claim +ₑ w *ₑ v}
        w := w *ₑ gamma
    let mut rounds := []
    let mut chals := []
    for _ in [:g.stepVars] do
      let (next, k', cs, wire) ← proveFold ro k poly
      poly := next
      k := k'
      rounds := wire :: rounds
      chals := cs :: chals
    if i == 0 then
      maskClaim := dot cm.mask ((List.range cm.mask.length).map (kernelCoeff k))
      absorb ro [77, 65, 83, 75, 95, 67, 76, 65, 73, 77] (exts [maskClaim])
      beta ← challenge ro [77, 65, 83, 75, 95, 66, 69, 84, 65]
      guard (beta != QuinticGoldilocks.zero && decide (poly.size ≤ cm.mask.length))
      poly := cm.mask.toArray.mapIdx fun j m => (poly[j]?.getD .zero) +ₑ beta *ₑ m
      k := {k with claim := k.claim +ₑ beta *ₑ maskClaim}
    let data := {c.stage.data with
      foldWords := rounds.reverse.flatten.flatMap limbs
      oodWords := ood.flatMap limbs}
    prev := some ({c with stage := {c.stage with data}}, chals.reverse)
  let some (last, cs) := prev | failure
  absorb ro [70, 73, 78, 65, 76, 95, 80, 79, 76, 89] (exts poly.toList)
  let (payload,_) ← revealStage ro last cs beta
  return ((payload :: stages).reverse, limbs maskClaim, poly.toList.flatMap limbs)

end Qsag.MultiDepthQrom.IvcAlgebra
end
