module
public import Qsag.Protocol.Aggregation.QuinticMultiStageWhir
public import QsagWhirVerified.Types
public import QsagWhirVerified.WireBounds
public section
open Aeneas Aeneas.Std
namespace qsag_whir_verified.proofs

abbrev wireFold {F : Type} (read : Nat → Option F)
    (bridge : F → F → F → F → F → F → CwyzFoldChals → F)
    (len pos : Nat) (claim : F) (c : CwyzFoldChals) : Option F := do
  if pos + 200 ≤ len then
    let a ← read pos
    let b ← read (pos + 40)
    let d ← read (pos + 80)
    let f ← read (pos + 120)
    let g ← read (pos + 160)
    some (bridge a b d f g claim c)
  else none

abbrev qsagFold (read : Nat → Option Qsag.QuinticGoldilocks)
    (abs : Fp5 → Qsag.QuinticGoldilocks) (len : Nat) :=
  wireFold read (fun a b d f g claim c => Qsag.hemBridgeFoldClaim claim a b d f g
    (abs c.phi) (abs c.theta) (abs c.alpha) (abs c.beta)) len

@[expose] def foldMessages {F : Type}
    (step : Nat → F → CwyzFoldChals → Option F) (pos : Nat) (claim : F) :
    List CwyzFoldChals → Option F
  | [] => some claim
  | c :: cs => do
    let next ← step pos claim c
    foldMessages step (pos + 200) next cs

abbrev fieldRegion (word : Nat → Nat) (len pos count : Nat) (prime : Nat := Qsag.goldilocksPrime) : Option Usize := do
  let e ← boundedEnd len pos count 40
  if validWordRegion word prime len pos e.val then some e else none

abbrev stageRegion (word : Nat → Nat) (len pos : Nat) (s : StageEnvelope)
    (base : Bool) (terminal : Nat) (profile : Option Qsag.Aggregation.PublicHemQuintic128) :
    Option Usize := do
  if s.step_vars.val = 0 ∨ 6 < s.step_vars.val then none else
    let after ← fieldRegion word len pos (5 * s.step_vars.val)
    let opening ← if terminal = 0 then do
        let root ← digestRegion word len after.val 1 profile
        fieldRegion word len root.val 2
      else fieldRegion word len after.val terminal
    let (_, e) ← openingRegion word len opening.val s.log_leaves.val s.step_vars.val
      (s.indices.val.map UScalar.val) base profile
    some e

abbrev scheduleCounts (rows early a b c d count : Nat) : Prop :=
  let log := rows + 8
  rows ≤ 20 ∧ a ≤ 6 ∧ b ≤ 6 ∧ c ≤ 6 ∧ d ≤ 6 ∧ 16 ≤ log ∧ log ≤ 28 ∧
    count = (if log ≤ 22 then 3 else 4) ∧ 1 ≤ early ∧ early ≤ 8 ∧ early + (a+b+c+d) = log

abbrev scheduleFits (rows early : Nat) (stages : PayloadStages) : Prop :=
  scheduleCounts rows early stages.first.step_vars.val stages.second.step_vars.val stages.third.step_vars.val
    ((stages.fourth.map (fun s => s.step_vars.val)).getD 0) (if stages.fourth.isSome then 4 else 3)

abbrev payloadWire {F : Type} (word : Nat → Nat) (row : Usize → Option F)
    (len rows early : Nat) (profile : Option Qsag.Aggregation.PublicHemQuintic128)
    (stages : PayloadStages) : Option F := do
  if scheduleFits rows early stages then
    let r ← digestRegion word len 0 1 profile
    let claim ← row r
    let cols ← boundedEnd len r.val rows 360
    let ood ← fieldRegion word len cols.val 256
    let folds ← fieldRegion word len ood.val 5
    let b ← stageRegion word len folds.val stages.first true 0 profile
    let c ← stageRegion word len b.val stages.second false 0 profile
    let terminal := 2^early + 2
    let stop ← match stages.fourth with
      | none => stageRegion word len c.val stages.third false terminal profile
      | some fourth => do
          let d ← stageRegion word len c.val stages.third false 0 profile
          stageRegion word len d.val fourth false terminal profile
    if stop.val = len then some claim else none
  else none

end qsag_whir_verified.proofs
end
