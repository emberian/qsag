module
/-
# Qsag.Tactic.AssuranceKit — `0-Classical` Proof Automation & Constructive Assurance Gates

Reusable Lean 4.35 tactic and command-elaboration infrastructure for QSAG (`LAW-M2`). This module
is proof support below every library layer: it imports `Qsag.Tactic.Prelude` and `Lean` only.
1. **`#verify_constructive <ident>+`**:
   Compile-time kernel axiom and `Prop`-type auditor enforcing `0 sorryAx`, `0` custom axioms,
   `0` compiler-trust axioms (`_native` / `ofReduceBool`), and **`0` transitive `Classical.choice`**
   (`axioms ⊆ {propext, Quot.sound}`).
2. **`#tooth_pair <secIdent> vs <toothIdent>`**:
   Compile-time structural pairing auditor verifying that a security theorem is paired with a
   structurally related counterexample/refusal theorem and that both satisfy
   `#verify_constructive` without vacuous `False` hypotheses.
   Shared primitive carriers do not establish a pair; a domain operation or predicate must overlap.
   This is a structural diagnostic, not a proof that the tooth is a mutation of the theorem.
   `#verify_inhabited` constructs one joint assignment for all theorem binders, including
   propositions and dependent values; witness parameters must themselves be constructible.
3. **`by bv_xor_cancel`**:
   Constructive (`0 Classical.choice`, `0 ofReduceBool`) XOR one-time-pad normalizer and
   unbounded reflected AC normalization over `BitVec w`; a Boolean fallback handles
   other bitwise identities over `UInt64`, `UInt8`, and `Bool`.
4. **`by frame_prefix_inj`**:
   Peels length-framed equalities (`frameList`) in the context, preserving every remainder.

The tactics that depend on library definitions live with those definitions:
`mask_bijection_hop` and the `SimpleEquiv` pad combinators in `Qsag.Math.Tactic.MaskBijection`,
`compose_forward_sim` and `mir_sim_step` in `Qsag.Exec.Tactic.SimulationKit`.
-/

public import Qsag.Tactic.Prelude
public meta import Lean
