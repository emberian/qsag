module
/-
# Qsag.Protocol.Aggregation.CorduroyAndHemAirCompleteness — Algebraic `Corduroy` Hypertree & `Hem` Opcode Semantics

Constructive, zero-axiom, zero-`Classical.choice` formalization of:
1. **`Corduroy` Algebraic Poseidon2 Hypertree Spec & Threshold Matched-Input Bit-Identity (`corduroy_threshold_matches_standalone`):**
   - `CorduroyParams` (`h = 28, d = 7` -> `4`-bit subtree height, `w = 4, ell1 = 128, targetSum = 192, forsTrees = 33, forsHeight = 6`), width-12 `Goldilocks` `Poseidon2` sponge (`rate = 8, capacity = 4`, 4-limb `Lane4` digest), injective tweakable `CorduroyAdrs` framing, WOTS+C `targetSum` checksum-free counter grinding, and FORS/TSW bottom layer matching `crates/qsag-core/src/corduroy.rs` and `crates/qsag-agg/src/sig.rs`.
   - Standalone signing completeness (`corduroyVerify_corduroySign`) and dealerless `(t, n)` Shamir/SPDZ share-level `Poseidon2` threshold bit-identity (`corduroy_threshold_matches_standalone`).
2. **Constructive `Corduroy` Multi-Target EUF-CMA Witness Extractor (`corduroy_euf_cma_extract`):**
   - Constructive `Type`-valued (`0 Classical.choice`) extractor over `q_sig` signing queries producing an explicit `CorduroyBreak`:
     - `CorduroyBreak.msgHashCollision`: distinct `(R, pk, msg) ≠ (R', pk, msg')` mapping to the same leaf index + message digest;
     - `CorduroyBreak.spongeTweakCollision`: distinct `(adrs1, in1) ≠ (adrs2, in2)` producing the same 4-Goldilocks-limb sponge output along the hypertree, FORS, or WOTS `T_ℓ` compression;
     - `CorduroyBreak.wotsChainPreimage`: explicit WOTS+C chain link inversion `d* < d_honest` via target-sum conservation (`wotsTargetSum_reused_smaller_digit`).
3. **256-column `Hem` opcode and selector semantics:**
   - Bounded limb decomposition, no-wrap digit unpacking, and exact guard/functional-transition
     decomposition for every scheduled opcode.
   - `hemStepTraceValid_iff_stepOp256TableOk` proves equivalence of the selector-explicit
     table and the original 256-column table; it does not extract a native signature.

For both aggregation profiles an accepted active slot extracts a native signature
(`stepOp256TableOk_xmss_extract`, `stepOp256TableOk_corduroy_extract`) and the extracted committee
gives an accepted serialized signer-witness trace (`xmssMachineToExecutionTrace_accepts`,
`corduroyMachineToExecutionTrace_accepts`). Conversely, for the `XmssPoseidon2` profile every
natively accepted signature yields an accepted table (`stepXmssRows_of_verify`, committees with
inactive slots in `stepXmssSlotsRows_of_verify`); the corresponding constructor for the
`CorduroyPoseidon2` profile is not built. The custody geometry above is distinct from the
aggregation geometry (16 layers, 32 FORS trees of height 8); the two must not be identified.
-/

public import Qsag.Protocol.Aggregation.CorduroyAndHemAirCompleteness.GoldilocksPoseidon2Foundations
public import Qsag.Protocol.Aggregation.CorduroyAndHemAirCompleteness.CorduroyHypertreeEufCma
public import Qsag.Protocol.Aggregation.CorduroyAndHemAirCompleteness.CorduroyThresholdEngine
public import Qsag.Protocol.Aggregation.CorduroyAndHemAirCompleteness.StepOp256SelectorEquiv
public import Qsag.Protocol.Aggregation.CorduroyAndHemAirCompleteness.StepOp256RowSemantics
public import Qsag.Protocol.Aggregation.CorduroyAndHemAirCompleteness.StepOp256WotsChainRows
public import Qsag.Protocol.Aggregation.CorduroyAndHemAirCompleteness.StepOp256XmssExtraction
public import Qsag.Protocol.Aggregation.CorduroyAndHemAirCompleteness.StepOp256CorduroyExtraction
public import Qsag.Protocol.Aggregation.CorduroyAndHemAirCompleteness.XmssStepOpForward
