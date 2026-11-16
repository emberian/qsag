module
public import Qsag.Tactic.Prelude

/-!
Shared wire data for adaptively scheduled threshold-signing sessions. Protocol guards and
executable network games use these same carriers; no execution engine is imported here.
-/
public section
namespace Qsag
set_option autoImplicit false

/-- Exact observable abort classification emitted by real and ideal threshold signing sessions. -/
inductive AbortReason where
  | quorumRejected
  | walPoisoned
  | walPkMismatch
  | walEpochRejected
  | round1CommitMismatch (culprit : Nat)
  | activeConsistencyFailed
  | cutOpenMismatch (culprit : Nat)
  deriving DecidableEq, Repr

/-- Exact observable outcome of a signing session delivered to the rushing adversary. -/
inductive SessionOutcome where
  | signOk (sigBytes : ByteArray)
  | abort (reason : AbortReason)
  deriving DecidableEq

/-- Adaptive session scheduling directive chosen by `UcRushingAdversary`. -/
structure SessionScheduleReq where
  sessionId       : Nat
  reqEpoch        : Nat
  msg             : List UInt8
  optRand         : List UInt8
  honestApprovers : List Nat
  deriving DecidableEq, Repr

end Qsag
end
