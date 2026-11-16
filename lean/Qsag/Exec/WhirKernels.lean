module
public import Qsag.Protocol.Aggregation.Aggregation
import Qsag.Tactic.AssuranceKit
/-! Executable WHIR kernels over the canonical quartic carrier. The MIR weld imports
this owner directly, so legacy oracle experiments do not enter its dependency graph. -/
public section
namespace Qsag.Exec
open Qsag Aggregation
/-- Extracted `qsag_whir_verified::duet_fold`: `odd + alpha * even`. -/
def hemDuetFold (v0 v1 : GoldilocksExt4) (invTwoY0 invTwo : Goldilocks)
    (alpha : GoldilocksExt4) : GoldilocksExt4 :=
  let even := GoldilocksExt4.mul (GoldilocksExt4.add v0 v1) (GoldilocksExt4.embedBase invTwo)
  let odd := GoldilocksExt4.mul (GoldilocksExt4.sub v0 v1) (GoldilocksExt4.embedBase invTwoY0)
  GoldilocksExt4.add odd (GoldilocksExt4.mul alpha even)

/-- Extracted `qsag_whir_verified::fold_duet_affine_ext4` (`cwyz_duet_fold`), defined directly
    via `Qsag.Aggregation.foldDuetExt4` on the asymmetric `even + theta * odd` coset combination. -/
@[expose] def hemAffineDuetFold (v0 v1 : GoldilocksExt4) (x : Goldilocks)
    (theta alpha beta : GoldilocksExt4) : GoldilocksExt4 :=
  let half := Goldilocks.inv (Goldilocks.ofNat 2)
  let invTwoX := Goldilocks.mul half (Goldilocks.inv x)
  let odd := GoldilocksExt4.mul (GoldilocksExt4.sub v0 v1) (GoldilocksExt4.embedBase invTwoX)
  let mixed := foldDuetExt4 v0 v1 invTwoX half theta
  let chal := GoldilocksExt4.add alpha
    (GoldilocksExt4.mul beta (GoldilocksExt4.embedBase (Goldilocks.mul x x)))
  GoldilocksExt4.add odd (GoldilocksExt4.mul chal mixed)

/-- Extracted `qsag_whir_verified::cwyz_bridge_claim_step` dual linear-functional sumcheck bridge. -/
def hemBridgeClaimStep
    (eval0 eval1 eval2 eval3 eval4 claim phi theta alpha beta : GoldilocksExt4) : GoldilocksExt4 :=
  let f := GoldilocksExt4.add eval0 (GoldilocksExt4.mul phi eval1)
  let g := GoldilocksExt4.add eval2 (GoldilocksExt4.mul phi (GoldilocksExt4.sub claim eval0))
  let core := GoldilocksExt4.add g (GoldilocksExt4.mul alpha
    (GoldilocksExt4.add f (GoldilocksExt4.mul theta g)))
  let shift := GoldilocksExt4.mul beta (GoldilocksExt4.add eval3 (GoldilocksExt4.mul theta eval4))
  GoldilocksExt4.add core shift

def hemHorner (coeffs : List Aggregation.GoldilocksExt4) (z : Goldilocks)
    (init : Aggregation.GoldilocksExt4 := Aggregation.GoldilocksExt4.zero) :
    Aggregation.GoldilocksExt4 :=
  coeffs.foldr (fun c acc => Aggregation.GoldilocksExt4.add
    (Aggregation.GoldilocksExt4.mul acc (Aggregation.GoldilocksExt4.embedBase z)) c) init

theorem hemHorner_nil (z : Goldilocks) (init : Aggregation.GoldilocksExt4) :
    hemHorner [] z init = init := by rfl

theorem hemHorner_cons (c : Aggregation.GoldilocksExt4) (rest : List Aggregation.GoldilocksExt4)
    (z : Goldilocks) (init : Aggregation.GoldilocksExt4) :
    hemHorner (c :: rest) z init = Aggregation.GoldilocksExt4.add
      (Aggregation.GoldilocksExt4.mul (hemHorner rest z init)
        (Aggregation.GoldilocksExt4.embedBase z)) c := by rfl

#export_eqns hemDuetFold hemAffineDuetFold hemBridgeClaimStep
end Qsag.Exec
end
