module

public import QsagVerified.Proofs.KeccakWitness.Group0
public import QsagVerified.Proofs.KeccakWitness.Group1
public import QsagVerified.Proofs.KeccakWitness.Group2
public import QsagVerified.Proofs.KeccakWitness.Group3
public import QsagVerified.Proofs.KeccakWitness.Group4
public import QsagVerified.Proofs.KeccakWitness.Group5
public import QsagVerified.Proofs.KeccakWitness.Group6
public import QsagVerified.Proofs.KeccakWitness.Group7



public section

namespace qsag_verified.proofs
open Aeneas Aeneas.Std qsag_verified

theorem keccak_f1600_zero_state_nonconstant :
    ∃ out, keccak.keccak_f1600 (Std.Array.repeat 25#usize 0#u64) = .ok out ∧
      out ≠ Std.Array.repeat 25#usize 0#u64 := by
  refine ⟨(keccakZeroRound 24), ?_, ?_⟩
  · have hz : Std.Array.repeat 25#usize 0#u64 = keccakZeroRound 0 := rfl
    rewrite [hz]
    unfold keccak.keccak_f1600
    apply bind_ok_step zero_round_0
    apply bind_ok_step zero_round_1
    apply bind_ok_step zero_round_2
    apply bind_ok_step zero_round_3
    apply bind_ok_step zero_round_4
    apply bind_ok_step zero_round_5
    apply bind_ok_step zero_round_6
    apply bind_ok_step zero_round_7
    apply bind_ok_step zero_round_8
    apply bind_ok_step zero_round_9
    apply bind_ok_step zero_round_10
    apply bind_ok_step zero_round_11
    apply bind_ok_step zero_round_12
    apply bind_ok_step zero_round_13
    apply bind_ok_step zero_round_14
    apply bind_ok_step zero_round_15
    apply bind_ok_step zero_round_16
    apply bind_ok_step zero_round_17
    apply bind_ok_step zero_round_18
    apply bind_ok_step zero_round_19
    apply bind_ok_step zero_round_20
    apply bind_ok_step zero_round_21
    apply bind_ok_step zero_round_22
    exact zero_round_23
  · intro h
    have first := congrArg (fun a : Std.Array Std.U64 25#usize => a.val.getD 0 0#u64) h
    exact (by decide : (17376452488221285863#u64 : Std.U64) ≠ 0#u64) first

end qsag_verified.proofs
