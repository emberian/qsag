module
public import Qsag.Exec.RssParticipantGateWeights
meta import Qsag.Exec.RssParticipantGateWeights
public import Qsag.Exec.RssParticipantGateField
meta import Qsag.Exec.RssParticipantGateField
public import Qsag.Exec.RssParticipantGateChecks
meta import Qsag.Exec.RssParticipantGateChecks
public import Qsag.Protocol.Migration.ActiveMigrationZeroTest
meta import Qsag.Protocol.Migration.ActiveMigrationZeroTest
public import Qsag.Math.Gf2Pow128
meta import Qsag.Math.Gf2Pow128
public section
open Qsag Qsag.RssParticipant Qsag.RssParticipant.GateChecks Qsag.MigrationExecution

private def honest : PolyCommitment :=
  let x := 0x1234#128
  let y := 0x5678#128
  let rx := 0x9#128
  let ry := 0xabc#128
  ⟨x, y, rustGf128Mul x y, rx, ry, rustGf128Mul rx ry,
    rustGf128Mul rx y ^^^ rustGf128Mul x ry⟩

def Qsag.RssParticipant.GateChecks.runWeightedGateChecks : IO Unit := do
  let challenges := [0#128, 1#128, 2#128, 0x123#128, 0xfedcba9876543210#128]
  if !(challenges.all (polyAccepts honest)) then
    throw (IO.userError "honest final product rejected")
  let forged := { honest with claim := honest.claim ^^^ 1#128 }
  if !(polyAccepts forged 0#128) then
    throw (IO.userError "zero challenge negative control unexpectedly rejected")
  if (challenges.drop 1).any (polyAccepts forged) then
    throw (IO.userError "tampered claim accepted at a nonzero test challenge")
  let ts := [towerZero 7, towerOne 7, towerX 7]
  if !(ts.all (fun t => accepts (lateForgery t) t)) then
    throw (IO.userError "late-commitment forgery control failed")
  let zeroGate : GateRecord := ⟨0, 0, 0, 0, 0⟩
  let badGate : GateRecord := { zeroGate with product := 1 }
  let badTable : GateTable 1 :=
    .branch (.leaf (zeroGate, zeroGate, zeroGate)) (.leaf (badGate, zeroGate, zeroGate))
  let weightedAccept := fun g => decide
    (weightEval (.cons g .nil) (claimedCoeffs badTable) =
      weightEval (.cons g .nil) (trueCoeffs badTable))
  if !(weightedAccept (towerZero 7)) || (ts.drop 1).any weightedAccept then
    throw (IO.userError "tampered gate weight-root control failed")
  IO.println "weighted gate and final product checks: honest accepted; fixed tampered claim rejected at four nonzero coins; tau=0 collision and late-commitment forgery controls confirmed"
end

#eval Qsag.RssParticipant.GateChecks.runWeightedGateChecks
