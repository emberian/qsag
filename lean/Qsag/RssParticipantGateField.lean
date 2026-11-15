module
public import Qsag.RssParticipantGateChecks
public import Qsag.Tower128PolyBasisIso
import all Qsag.RssParticipantGateChecks
import all Qsag.Tower128PolyBasisIso
import all Qsag.ActiveMigrationZeroTest
import all Qsag.BinaryTower
import all Qsag.Rss256TernaryRound
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
    hS.map (fun a b h => polyToTower128_injective a b h)
  have hc := false_final_accepting_challenges_le_two c.toTower ht (S.map polyToTower128) hmap
  rw [filter_map_len] at hc
  simpa only [polyAccepts_eq] using hc

#verify_constructive polyAccepts_eq poly_false_final_challenges_le_two
end Qsag.RssParticipant.GateChecks
end
