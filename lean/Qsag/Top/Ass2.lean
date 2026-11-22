module
/-
# Qsag.Top.Ass2 — the `ASS2 / Dregg-64` enclave ISA

Composition of the `ASS2 / Dregg-64` development:

1. `Qsag.Machine.Ass2Dregg64Codec`: the instruction syntax and the 32-bit codec, a bijection
   between well-formed instructions and accepted words (`decodeAss2_encodeAss2`,
   `encodeAss2_decodeAss2`).
2. `Qsag.Machine.Ass2Dregg64Isa`: the architectural state and the total step function, with the
   cryptographic instructions defined by `Goldilocks`, `QuinticGoldilocks`, `Math.Gf2Pow128`,
   `keccakF1600`, `Poseidon2Gl24.poseidon2Gl24Perm` and `poseidon2Perm12`.
3. `Qsag.Machine.Ass2DitNoninterference`: noninterference of the `PC`, address, `CYCLES` and
   `INSTRET` trace, the `Spec.DitHardwareContract` instance `ass2DitContract`, and the verified
   `zk-Hem v2` Horner / `TurboSHAKE256` leaf kernel.

`ass2_straight_line_program_constant_time` states the three together for an arbitrary
straight-line program: its encoding runs as the fold of the instruction semantics, and its trace
does not depend on anything secret.
-/

public import Qsag.Machine.Ass2Dregg64Codec
public import Qsag.Machine.Ass2Dregg64Isa
public import Qsag.Machine.Ass2DitNoninterference
public import Qsag.Spec.Assumptions
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag.Ass2

set_option autoImplicit false

/-- **Straight-line enclave code is constant time by construction.** Let `prog` be a list of
    well-formed instructions without control transfers, memory accesses or control-register
    accesses, loaded at an aligned `PC` in a running machine, with public code bytes. Then the
    run of `prog.length` steps is the fold of `execAss2` over `prog`, and any state that agrees
    on the public part yields the same `PC`, address, `CYCLES` and `INSTRET` trace and an
    equivalent final state. Registers and lanes may all be secret. -/
theorem ass2_straight_line_program_constant_time (prog : List Ass2Insn)
    (hprog : ∀ i, i ∈ prog → i.WellFormed ∧ i.isStraight = true)
    (cfg : PubCfg) (s₁ s₂ : Ass2State) (heq : Ass2PubEquiv cfg s₁ s₂)
    (hh : s₁.halted = false) (hpc : s₁.pc.toNat % 4 = 0)
    (hl : LoadedAt s₁.mem s₁.pc prog) (hcode : CodePub cfg.mem s₁.pc prog.length) :
    runAss2 prog.length s₁ = prog.foldl (fun t i => execAss2 i t) s₁ ∧
    traceAss2 prog.length s₁ = traceAss2 prog.length s₂ ∧
    Ass2PubEquiv (cfgRun prog.length cfg s₁) (runAss2 prog.length s₁) (runAss2 prog.length s₂) :=
  ⟨runAss2_straight prog s₁ hh hpc hl hprog,
    ass2_dit_run_trace_noninterference prog.length cfg s₁ s₂ heq
      (ditSafeRun_straight prog cfg s₁ hh hpc hl hcode hprog)⟩

#verify_constructive
  Qsag.Ass2.ass2_straight_line_program_constant_time

end Qsag.Ass2
