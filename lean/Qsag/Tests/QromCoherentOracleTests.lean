module
public import Qsag.Math.GoldilocksBase
/- Executed coherent superposition and database-measurement controls. -/
public import Qsag.Protocol.Aggregation.HemOpening
public import Qsag.Oracle.Qrom
public import Qsag.Tests.OracleAndQrom
public import Qsag.Protocol.Aggregation.MultiRoundFsQrom
public import Qsag.Protocol.Aggregation.QromSaltedMerkleStateRestoration
public import Qsag.Protocol.Aggregation.Cwyz26EqualDegreeAndMultiFold
public import Qsag.Coding.Cwyz26
public import Qsag.Protocol.Aggregation.Cwyz26JohnsonCertificate
public import Qsag.Math.Counting
public import Qsag.Math.CoeffPoly
public import Qsag.Math.PolyRing
public import Qsag.Math.HasseHensel
public import Qsag.Coding.Resultant
public import Qsag.Coding.GuruswamiSudan
public import Qsag.Coding.ReedSolomon
public import Qsag.Protocol.Aggregation.HemRbrSoundness
public import Qsag.Protocol.Aggregation.ConcreteSecurityBudget
public import Qsag.Math.Goldilocks

public section
namespace Qsag
set_option autoImplicit false

/-! `coherent_hem_decoder_execution` (the actual authenticated Hem decoder consumer on the one-bit toy
layout) is proved in `Protocol/Aggregation/HemOpening`: the Hem event is shown pointwise equal to the toy
acceptance event there, and the coherent mass is executed in `Oracle/Qrom`
(`toy_coherent_accept_mass`). -/

#verify_constructive
  Qsag.coherent_hem_decoder_execution
/-! ## `w = 2` DFMS runtime witness and database-measurement tooth -/

/-! `dfmsW2ParityAdv`, `dfmsW2ParityEvent` and the real-oracle half of the witness are evaluated in
`Oracle/Qrom`; `dfmsW2TableEq`, `dfms_w2_coherent_runtime_witness` and
`tooth_dfms_w2_raw_database_measurement_disturbs` are executed in
`Protocol/Aggregation/QromSaltedMerkleStateRestoration`, where the DFMS runtime is visible. -/

#verify_constructive
  Qsag.dfms_w2_coherent_runtime_witness
  Qsag.tooth_dfms_w2_raw_database_measurement_disturbs

#tooth_pair dfms_projective_extraction_disturbance_bound vs tooth_dfms_w2_raw_database_measurement_disturbs

/-! ## Three-challenge equal-degree lift and intra-stage multi-fold budgets

Audits of the inhabitedness witnesses and `#tooth_pair` counterexamples of
`Qsag.Protocol.Aggregation.Cwyz26EqualDegreeAndMultiFold`, and of the upstream theorems that module
cites. -/

namespace Cwyz26EqualDegreeAndMultiFoldTests

/-! The fixtures (`gf`, `qf`, `dom16Out`, `dom32In`, the stage-profile accessors), the witnesses and the
teeth of this section are executed in `Protocol/Aggregation/Cwyz26EqualDegreeAndMultiFold`, in this same
namespace; this module audits and pairs them. -/

#verify_constructive
  Qsag.gsDecodeList_length_le_johnson

#verify_constructive
  Qsag.SylElim.bezout_space_finite_u_locus
  Qsag.SylElim.curve_leaf_gcd_decomp
  Qsag.SylElim.curve_three_poly_sheet_decomp

#verify_constructive inhabited_gsDecodeList_length_le_johnson
  tooth_gsDecodeList_johnson_denominator_needed
  inhabited_sliced_equal_degree_three_challenge_bound
  tooth_three_challenge_lo_pair_forgery
  inhabited_sliced_singleStep_bridge_four_challenge_bound
  tooth_bridge_four_challenge_forgery_exists

#verify_inhabited Qsag.gsDecodeList_length_le_johnson inhabited_gsDecodeList_length_le_johnson
#tooth_pair Qsag.gsDecodeList_length_le_johnson vs tooth_gsDecodeList_johnson_denominator_needed

#verify_inhabited Qsag.sliced_equal_degree_three_challenge_bound inhabited_sliced_equal_degree_three_challenge_bound
#tooth_pair Qsag.sliced_equal_degree_three_challenge_bound vs tooth_three_challenge_lo_pair_forgery


#verify_inhabited Qsag.sliced_singleStep_bridge_four_challenge_bound inhabited_sliced_singleStep_bridge_four_challenge_bound
#tooth_pair Qsag.sliced_singleStep_bridge_four_challenge_bound vs tooth_bridge_four_challenge_forgery_exists


end Cwyz26EqualDegreeAndMultiFoldTests

end Qsag
end
