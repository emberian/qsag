module
public import Qsag.Exec.RssParticipantGateChecks
public import Qsag.Math.Tower128PolyBasisIso
import all Qsag.Exec.RssParticipantGateChecks
import all Qsag.Math.Tower128PolyBasisIso
import all Qsag.Protocol.Migration.ActiveMigrationZeroTest
import all Qsag.Math.BinaryTower
import all Qsag.Protocol.Threshold.Rss256TernaryRound
import Qsag.Tactic.AssuranceKit

/-! Polynomial-basis adapter for the actual `keccak_mpc.rs` final product check.
Uses the already proved isomorphism to the degree-128 polynomial modulus.
This is an arithmetic representation bridge, not a packed64 evidence bridge. -/
public section
namespace Qsag.RssParticipant.GateChecks
open MigrationExecution Rss256ProductProof
set_option autoImplicit false
set_option maxRecDepth 8192

structure PolyCommitment where
  x : BitVec 128
  y : BitVec 128
  claim : BitVec 128
  rx : BitVec 128
  ry : BitVec 128
  c0 : BitVec 128
  c1 : BitVec 128

def PolyCommitment.toTower (c : PolyCommitment) : FinalCommitment :=
  ⟨polyToTower128 c.x, polyToTower128 c.y, polyToTower128 c.claim,
   polyToTower128 c.rx, polyToTower128 c.ry, polyToTower128 c.c0, polyToTower128 c.c1⟩

def polyAccepts (c : PolyCommitment) (tau : BitVec 128) : Bool :=
  decide (rustGf128Mul (c.rx ^^^ rustGf128Mul tau c.x) (c.ry ^^^ rustGf128Mul tau c.y) =
    c.c0 ^^^ rustGf128Mul tau c.c1 ^^^ rustGf128Mul (rustGf128Mul tau tau) c.claim)

theorem polyAccepts_eq (c : PolyCommitment) (tau : BitVec 128) :
    polyAccepts c tau = accepts c.toTower (polyToTower128 tau) := by
  apply decide_eq_decide_of_iff
  constructor
  · intro h
    have hh := congrArg polyToTower128 h
    simpa only [polyToTower128_mul_rust, polyToTower128_xor, PolyCommitment.toTower,
      finalOpening] using hh
  · intro h
    apply polyToTower128_injective
    simpa only [polyToTower128_mul_rust, polyToTower128_xor, PolyCommitment.toTower,
      finalOpening] using h

/-- Actual polynomial-basis checker, on any duplicate-free finite challenge set.
Fixed coefficients + uniform sampling gives ≤2/|S| conditional failure. -/
theorem poly_false_final_challenges_le_two (c : PolyCommitment)
    (hf : c.claim ≠ rustGf128Mul c.x c.y) (S : List (BitVec 128)) (hS : S.Nodup) :
    (S.filter (polyAccepts c)).length ≤ 2 := by
  have ht : c.toTower.claim ≠ towerMul 7 c.toTower.x c.toTower.y := by
    intro h
    apply hf
    apply polyToTower128_injective
    simpa only [polyToTower128_mul_rust, PolyCommitment.toTower] using h
  have hmap : (S.map polyToTower128).Nodup :=
    hS.map polyToTower128 (fun a b hab h => hab (polyToTower128_injective a b h))
  have hc := false_final_accepting_challenges_le_two c.toTower ht (S.map polyToTower128) hmap
  rw [filter_map_len] at hc
  have hp : polyAccepts c = fun t => accepts c.toTower (polyToTower128 t) :=
    funext (polyAccepts_eq c)
  rw [hp]
  exact hc

/-- A 64-bit Boolean relation word embeds below degree64 in the actual degree128
polynomial field; no coefficient can disappear in this embedding. -/
def wordToField (w : UInt64) : Tower128 :=
  polyToTower128 (w.toBitVec.setWidth 128)

theorem wordToField_eq_zero_iff (w : UInt64) :
    wordToField w = towerZero 7 ↔ w = 0 := by
  constructor
  · intro h
    have hb := (polyToTower128_eq_zero_iff _).mp h
    apply UInt64.eq_of_toBitVec_eq
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have he := congrArg (fun v : BitVec 128 => v.getLsbD i) hb
    simpa [BitVec.getLsbD_setWidth, show i < 128 by omega] using he
  · intro h
    subst w
    exact polyToTower128_zero

theorem wordToField_xor (a b : UInt64) :
    wordToField (a ^^^ b) = towerAdd 7 (wordToField a) (wordToField b) := by
  unfold wordToField
  rw [UInt64.toBitVec_xor, BitVec.setWidth_xor, polyToTower128_xor]

def gateError (g0 g1 g2 : GateRecord) : Tower128 :=
  wordToField ((g0.product ^^^ g1.product ^^^ g2.product) ^^^
    ((g0.lhsOwn ^^^ g1.lhsOwn ^^^ g2.lhsOwn) &&&
      (g0.rhsOwn ^^^ g1.rhsOwn ^^^ g2.rhsOwn)))

theorem gateError_zero_iff (g0 g1 g2 : GateRecord) :
    gateError g0 g1 g2 = towerZero 7 ↔ relation g0 g1 g2 := by
  unfold gateError
  rw [wordToField_eq_zero_iff, UInt64.xor_eq_zero_iff]
  rfl

#verify_constructive polyAccepts_eq poly_false_final_challenges_le_two
  wordToField_eq_zero_iff gateError_zero_iff wordToField_xor
end Qsag.RssParticipant.GateChecks
end
