module

public import Qsag.Top.ClosedProtocolReductions
public import Qsag.Top.Credentials
public import Qsag.Protocol.Signing.Compact1122ClosedEufCma
public import Qsag.Protocol.Threshold.MultiSessionMacBlindHybrid
public import Qsag.Math.Q192BernoulliTailBound
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag.Top

set_option autoImplicit false


/-- One weight of the three-tap matrix exceeds the proposed imbalance limit. -/
theorem tooth_legacy_balance_premise_false_for_three_tap_row :
    ¬ (∀ w ∈ Qsag.TapRowBias.prodRow0Weights, Qsag.TapRowBias.imbalance 32768 w ≤ 2047) :=
  Qsag.TapRowBias.prodRow0_balance_premise_fails.1

#verify_constructive Qsag.Top.tooth_legacy_balance_premise_false_for_three_tap_row

end Qsag.Top
end
