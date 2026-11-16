module

public import Qsag.Machine.MirSpecBridgeCore
public import Qsag.Machine.MirSpecBridgeWitnesses

/-! Public entry point for the hand-written MIR guard models, their four-layer
simulation chain, generalized `ShamirThresholdSubset` multi-turn safety, and concrete
accepted/rejected trace witnesses (all proved in `MirSpecBridgeCore`; `inhabited_four_layer_chain`
and `shamirSubset_preserves_multiturn_safety` are in its §7). The extracted Rust-to-model welds
live in the separate `qsag_aeneas` package (`AuthenticatedBeltAndRealSpecWeld.lean`,
`RealSpecGuardBoundary.lean`). -/
