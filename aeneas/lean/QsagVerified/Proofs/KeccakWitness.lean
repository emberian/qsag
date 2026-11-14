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

@[expose] def keccakZeroExpected : Std.Array Std.U64 25#usize :=
  Std.Array.make 25#usize [
    17376452488221285863#u64, 9571781953733019530#u64, 15391093639620504046#u64, 13624874521033984333#u64, 10027350355371872343#u64,
    18417369716475457492#u64, 10448040663659726788#u64, 10113917136857017974#u64, 12479658147685402012#u64, 3500241080921619556#u64,
    16959053435453822517#u64, 12224711289652453635#u64, 9342009439668884831#u64, 4879704952849025062#u64, 140226327413610143#u64,
    424854978622500449#u64, 7259519967065370866#u64, 7004910057750291985#u64, 13293599522548616907#u64, 10105770293752443592#u64,
    10668034807192757780#u64, 1747952066141424100#u64, 1654286879329379778#u64, 8500057116360352059#u64, 16929593379567477321#u64
  ]

theorem keccak_f1600_zero_state_exact :
    keccak.keccak_f1600 (Std.Array.repeat 25#usize 0#u64) =
      .ok (keccakZeroRound 24) := by
  have hz : Std.Array.repeat 25#usize 0#u64 = keccakZeroRound 0 := rfl
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

theorem keccak_f1600_zero_state_nist :
    keccak.keccak_f1600 (Std.Array.repeat 25#usize 0#u64) =
      .ok keccakZeroExpected := keccak_f1600_zero_state_exact

theorem keccak_zero_expected_lane0 :
    keccakZeroExpected.val.getD 0 0#u64 = 0xF1258F7940E1DDE7#u64 := rfl

theorem keccak_f1600_zero_state_nonconstant :
    ∃ out, keccak.keccak_f1600 (Std.Array.repeat 25#usize 0#u64) = .ok out ∧
      out ≠ Std.Array.repeat 25#usize 0#u64 := by
  refine ⟨keccakZeroExpected, keccak_f1600_zero_state_nist, ?_⟩
  intro h
  have first := congrArg (fun a : Std.Array Std.U64 25#usize => a.val.getD 0 0#u64) h
  exact (by decide : (17376452488221285863#u64 : Std.U64) ≠ 0#u64) first

end qsag_verified.proofs
