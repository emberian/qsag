module
public import Qsag.Exec.RssParticipantPassiveSimulation
import all Qsag.Exec.RssParticipantPassiveSimulation
import all Qsag.Protocol.Aggregation.UcGames
import Qsag.Tactic.AssuranceKit

/-! The passive coupling preserves the finite tape length. This restricts the
bijection to the exact sample domain of a fixed-length independent tape; it does
not replace actual PRG resources or claim active/quantum trace simulation. -/
public section
namespace Qsag.RssParticipant
set_option autoImplicit false

theorem forwardTape_length (state : RssKState) (rounds : List PassiveRound) (tape : List KState) :
    (forwardTape state rounds tape).length = tape.length := by
  induction rounds generalizing state tape with
  | nil => rfl
  | cons round rounds ih =>
    cases tape with
    | nil => rfl
    | cons hidden tape => simp only [forwardTape, List.length_cons, ih]

theorem inverseTape_length (state : RssKState) (rounds : List PassiveRound) (tape : List KState) :
    (inverseTape state rounds tape).length = tape.length := by
  induction rounds generalizing state tape with
  | nil => rfl
  | cons round rounds ih =>
    cases tape with
    | nil => rfl
    | cons sample tape => simp only [inverseTape, List.length_cons, ih]

def fixedTapeEquiv (state : RssKState) (rounds : List PassiveRound) (length : Nat) :
    SimpleEquiv { tape : List KState // tape.length = length }
      { tape : List KState // tape.length = length } where
  toFun tape := ⟨forwardTape state rounds tape.val, (forwardTape_length _ _ _).trans tape.property⟩
  invFun tape := ⟨inverseTape state rounds tape.val, (inverseTape_length _ _ _).trans tape.property⟩
  left_inv tape := by apply Subtype.ext; exact inverse_forwardTape _ _ _
  right_inv tape := by apply Subtype.ext; exact forward_inverseTape _ _ _

theorem fixedTapeEquiv_inverse (state : RssKState) (rounds : List PassiveRound) (length : Nat)
    (tape : { tape : List KState // tape.length = length }) :
    (fixedTapeEquiv state rounds length).invFun ((fixedTapeEquiv state rounds length).toFun tape) = tape ∧
    (fixedTapeEquiv state rounds length).toFun ((fixedTapeEquiv state rounds length).invFun tape) = tape :=
  ⟨(fixedTapeEquiv state rounds length).left_inv tape, (fixedTapeEquiv state rounds length).right_inv tape⟩

#verify_constructive forwardTape_length inverseTape_length fixedTapeEquiv_inverse
end Qsag.RssParticipant
