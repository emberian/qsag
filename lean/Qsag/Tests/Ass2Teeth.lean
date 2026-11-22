module
public import Qsag.Top.Ass2
import Qsag.Tactic.AssuranceKit
/-
Teeth for the `ASS2 / Dregg-64` ISA (`Qsag.Top.Ass2`). Each tooth runs a mutant of one design
decision on a concrete state and exhibits the failure the decision prevents.

* `tooth_r0_aliased_pc_turns_sel_into_secret_branch`: if a write to register field `0` landed in
  `PC` (the `Absolute Ass` convention `R0 = PC`), `SEL` with a secret selector would be a secret
  branch. Against `ass2_r0_always_zero`.
* `tooth_secret_bnez_leaks_pc_trace`: `BNEZ` on a secret register fails `ditOk` and the two runs
  reach different `PC`s, while `SEL` on the same secret passes `ditOk` and they reach the same
  `PC`. Against `ass2_dit_step_noninterference`.
* `tooth_zero_word_traps_not_nop`: with `EXC_EN = 1` the all-zero word vectors to `EVEC`; a
  decoder reading it as `NOP` continues at `PC + 4`. Against `ass2_zero_word_traps_when_enabled`.
* `tooth_jalr_post_write_corrupts_self_call`: a `JALR` that writes the link register before
  reading the base jumps to `PC + 4` on `JALR R3, R3, 0`. Against `ass2_jalr_self_alias_safe`.

`ass2_zero_word_slides_when_exc_disabled` records the other half of the all-zero word: with
`EXC_EN = 0` the spec's formula `PC := PC + 4` makes it a no-op, so zero memory is a sled until
trap entry is enabled.
-/

public section
namespace Qsag.Ass2.Teeth

set_option autoImplicit false

/-- A running machine at `PC = 0x1000` with zero memory, `EVEC = 0x80`, traps enabled,
    `R1 = 0x100`, `R2 = 0x200` and `R3 = x`. -/
def secretState (x : UInt64) : Ass2State :=
  { pc := 0x1000,
    regs := fun r => if r = 3 then x else (if r = 1 then 0x100 else (if r = 2 then 0x200 else 0)),
    spg := fun _ => 0, mem := fun _ => 0, evec := 0x80, epc := 0, ecause := 0, excEn := true,
    halted := false, instret := 0, cycles := 0, dbgOut := [] }

/-- Everything is public except `R3`. -/
def r3Secret : PubCfg :=
  { reg := fun r => decide (r ≠ 3), lane := fun _ => true, mem := fun _ => true }

theorem secretState_equiv (x y : UInt64) :
    Ass2PubEquiv r3Secret (secretState x) (secretState y) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun r hr => ?_, fun _ _ => rfl,
    fun _ _ => rfl⟩
  by_cases h3 : r = 3
  · rw [h3] at hr
    exact absurd hr (by decide)
  · show (if r = 0 then (0 : UInt64)
        else (if r = 3 then x else (if r = 1 then 0x100 else (if r = 2 then 0x200 else 0)))) =
      (if r = 0 then (0 : UInt64)
        else (if r = 3 then y else (if r = 1 then 0x100 else (if r = 2 then 0x200 else 0))))
    rw [ite_eq_right h3, ite_eq_right h3]

theorem secretState_fetch (x : UInt64) :
    fetch32 (secretState x).mem (secretState x).pc = 0 := by
  show fetch32 (fun _ => 0) 0x1000 = 0
  decide

theorem secretState_safe (x : UInt64) : DitSafeStep r3Secret (secretState x) := by
  have hcur : currentInsn (secretState x) = some .exc :=
    currentInsn_of_fetch rfl (show (0x1000 : UInt64).toNat % 4 = 0 by decide)
      (by rw [secretState_fetch]; exact decodeAss2_zero)
  exact And.intro (fun _ _ => allBelow_of (fun _ _ => rfl)) (fun i hi => by
    rw [hcur] at hi
    cases hi
    rfl)

/-! ## 1. `PC` is not a general-purpose register -/

/-- Mutant register write of a machine whose register `0` is the program counter: a write to
    field `0` lands in `PC`. -/
def setRegAliased (s : Ass2State) (rd : Reg) (v : UInt64) : Ass2State :=
  if rd = 0 then { s with pc := v } else (s.setReg rd v).retire 1

/-- `SEL` on the mutant. -/
def selAliased (rd ra rb rc : Reg) (s : Ass2State) : Ass2State :=
  setRegAliased s rd (if s.rget rc = 0 then s.rget ra else s.rget rb)

/-- Two states that differ in the secret `R3` only. `SEL R0, R1, R2, R3` meets the side
    conditions and leaves both at the same `PC`; on the aliased mutant the two runs continue at
    different `PC`s. -/
theorem tooth_r0_aliased_pc_turns_sel_into_secret_branch :
    ∃ s₁ s₂ : Ass2State, Ass2PubEquiv r3Secret s₁ s₂ ∧ ditOk r3Secret (.sel 0 1 2 3) = true ∧
      (execAss2 (.sel 0 1 2 3) s₁).pc = (execAss2 (.sel 0 1 2 3) s₂).pc ∧
      (selAliased 0 1 2 3 s₁).pc ≠ (selAliased 0 1 2 3 s₂).pc :=
  ⟨secretState 0, secretState 1, secretState_equiv 0 1, rfl, rfl, by decide⟩

/-! ## 2. `SEL` against a secret branch -/

/-- `BNEZ R3` with `R3` secret fails the side condition and the two runs diverge; `SEL` with the
    same secret selector passes it and they do not. -/
theorem tooth_secret_bnez_leaks_pc_trace :
    ∃ s₁ s₂ : Ass2State, Ass2PubEquiv r3Secret s₁ s₂ ∧
      ditOk r3Secret (.br .bnez 3 8) = false ∧
      (execAss2 (.br .bnez 3 8) s₁).pc ≠ (execAss2 (.br .bnez 3 8) s₂).pc ∧
      ditOk r3Secret (.sel 4 1 2 3) = true ∧
      (execAss2 (.sel 4 1 2 3) s₁).pc = (execAss2 (.sel 4 1 2 3) s₂).pc :=
  ⟨secretState 0, secretState 1, secretState_equiv 0 1, rfl, by decide, rfl, rfl⟩

/-! ## 3. The all-zero word -/

/-- With `EXC_EN = 1`, a step that fetches the all-zero word vectors to `EVEC` with
    `ECAUSE = 2` (`EnvCall`), `EPC = PC + 4` and `EXC_EN` cleared. -/
theorem ass2_zero_word_traps_when_enabled (s : Ass2State) (hh : s.halted = false)
    (hpc : s.pc.toNat % 4 = 0) (hw : fetch32 s.mem s.pc = 0) (he : s.excEn = true) :
    (stepAss2 s).pc = s.evec ∧ (stepAss2 s).ecause = 2 ∧ (stepAss2 s).epc = s.pc + 4 ∧
    (stepAss2 s).excEn = false := by
  rw [stepAss2_eq_exec hh hpc (by rw [hw]; exact decodeAss2_zero)]
  exact (ass2_exc_untaken_advances s).2 he

/-- With `EXC_EN = 0`, a step that fetches the all-zero word continues at `PC + 4`: it does not
    halt, does not enable traps and leaves memory unchanged, so the next zero word does the
    same. The spec's remark that all-zero memory "traps/halts cleanly rather than sliding" holds
    with `EXC_EN = 1` only. -/
theorem ass2_zero_word_slides_when_exc_disabled (s : Ass2State) (hh : s.halted = false)
    (hpc : s.pc.toNat % 4 = 0) (hw : fetch32 s.mem s.pc = 0) (he : s.excEn = false) :
    (stepAss2 s).pc = s.pc + 4 ∧ (stepAss2 s).halted = false ∧ (stepAss2 s).excEn = false ∧
    (stepAss2 s).mem = s.mem ∧ (stepAss2 s).pc.toNat % 4 = 0 := by
  have e : execAss2 .exc s = s.retire 1 := by
    unfold execAss2
    dsimp only
    rw [ite_eq_right (by rw [he]; decide)]
    rfl
  rw [stepAss2_eq_exec hh hpc (by rw [hw]; exact decodeAss2_zero), e]
  exact ⟨rfl, hh, he, rfl, aligned_add4 _ hpc⟩

/-- Mutant decoder that reads the all-zero word as `NOP`. -/
def stepZeroIsNop (s : Ass2State) : Ass2State :=
  if fetch32 s.mem s.pc = 0 then execAss2 .nop s else stepAss2 s

/-- A machine with traps enabled at a zero word: the step vectors to `EVEC`, the mutant slides
    to `PC + 4`. -/
theorem tooth_zero_word_traps_not_nop :
    ∃ s : Ass2State, s.halted = false ∧ fetch32 s.mem s.pc = 0 ∧ s.excEn = true ∧
      (stepAss2 s).pc = s.evec ∧ (stepZeroIsNop s).pc = s.pc + 4 ∧
      (stepAss2 s).pc ≠ (stepZeroIsNop s).pc := by
  have h1 := (ass2_zero_word_traps_when_enabled (secretState 0) rfl (by decide)
    (secretState_fetch 0) rfl).1
  refine ⟨secretState 0, rfl, secretState_fetch 0, rfl, h1, by decide, ?_⟩
  rw [h1]
  decide

/-! ## 4. `JALR` reads its base before writing the link register -/

/-- Mutant `JALR` that writes the link register first and reads the base from the result. -/
def jalrPostWrite (rd ra : Reg) (off : BitVec 16) (s : Ass2State) : Ass2State :=
  (s.setReg rd (s.pc + 4)).retireTo
    (((s.setReg rd (s.pc + 4)).rget ra + (sext off <<< (2 : UInt64))) &&& ~~~3) 1

/-- `JALR R3, R3, 0` with `R3 = 0x2000`: the instruction jumps to `0x2000`; the mutant jumps to
    the return address `PC + 4`. -/
theorem tooth_jalr_post_write_corrupts_self_call :
    ∃ s : Ass2State, (execAss2 (.jalr 3 3 0) s).pc = s.rget 3 ∧
      (jalrPostWrite 3 3 0 s).pc = s.pc + 4 ∧
      (jalrPostWrite 3 3 0 s).pc ≠ (execAss2 (.jalr 3 3 0) s).pc :=
  ⟨secretState 0x2000, by decide, by decide, by decide⟩

/-! ## 5. The premises are inhabited -/

/-- Two states that differ in a secret register and a safe step from the first. -/
theorem dit_step_premises_inhabited :
    ∃ (cfg : PubCfg) (s₁ s₂ : Ass2State), Ass2PubEquiv cfg s₁ s₂ ∧ DitSafeStep cfg s₁ ∧
      s₁.regs 3 ≠ s₂.regs 3 :=
  ⟨r3Secret, secretState 5, secretState 9, secretState_equiv 5 9, secretState_safe 5, by decide⟩

/-- The memory image `05 ad de 40  55 f9 ee 3b  55 39 12 30  55 79 56 34` at address 0: the four
    words the reference model's `LI64(5, 0xDEADBEEF01234567)` emits. -/
def li64Image : Ass2State :=
  { pc := 0, regs := fun _ => 0, spg := fun _ => 0,
    mem := fun a =>
      [5, 173, 222, 64, 85, 249, 238, 59, 85, 57, 18, 48, 85, 121, 86, 52].getD a.toNat 0,
    evec := 0, epc := 0, ecause := 0, excEn := false, halted := false, instret := 0, cycles := 0,
    dbgOut := [] }

/-- The reference model's constant-load sequence is `loadImm64` and is loaded in `li64Image`. -/
theorem slk16_premises_inhabited :
    ∃ (x : UInt64) (rd : Reg) (s : Ass2State), rd ≠ 0 ∧ s.halted = false ∧
      s.pc.toNat % 4 = 0 ∧ LoadedAt s.mem s.pc (loadImm64 rd x) :=
  ⟨0xDEADBEEF01234567, 5, li64Image, by decide, rfl, by decide,
    ⟨by decide, by decide, by decide, by decide, trivial⟩⟩

/-- The literal binary kernel at PC zero, little-endian, with all other bytes zero. -/
def leafImage : Ass2State :=
  { li64Image with mem := fun a =>
      let w := zkhemLeafWords.getD (a.toNat / 4) 0
      (w >>> UInt32.ofNat (8 * (a.toNat % 4))).toUInt8 }

/-- Only the hundred instruction bytes and the architectural controls are public. -/
def leafLabels : PubCfg :=
  { reg := fun _ => false, lane := fun _ => false, mem := fun a => decide (a < 100) }

theorem leafImage_loaded : LoadedAt leafImage.mem 0 zkhemLeafProg := by
  repeat' first | exact True.intro | apply And.intro | decide

theorem leafImage_public : CodePub leafLabels.mem 0 25 := by
  repeat' first | exact True.intro | apply And.intro | (rw [memPub_four]; decide)

/-- An actual contract call on the literal image. Its two inputs select opposite child orders. -/
theorem leaf_contract_inhabited :
    ∃ pub d₁ d₂ : Ass2State, pub.halted = false ∧ pub.pc.toNat % 4 = 0 ∧
      LoadedAt pub.mem pub.pc zkhemLeafProg ∧ CodePub leafLabels.mem pub.pc 25 ∧
      (injectSecrets leafLabels pub d₁).rget 6 ≠ (injectSecrets leafLabels pub d₂).rget 6 ∧
      traceAss2 25 (injectSecrets leafLabels pub d₁) =
        traceAss2 25 (injectSecrets leafLabels pub d₂) := by
  let left := { leafImage with regs := fun r => if r = 4 then 12 else if r = 5 then 34 else 0 }
  let right := left.setReg 6 1
  refine ⟨leafImage, left, right, rfl, by decide, leafImage_loaded, leafImage_public, ?_,
    zkhemLeafEntry_trace leafLabels leafImage left right rfl (by decide)
      leafImage_loaded leafImage_public⟩
  rw [injectSecrets_secret_reg _ _ _ _ (by decide), injectSecrets_secret_reg _ _ _ _ (by decide)]
  decide +revert

/-- The base core traps at 0x0B. On a UART-equipped core a read to R0 consumes the
    first byte, the next read returns valid plus the second byte, and an empty read
    returns zero. Writes to the receive register trap in both profiles. -/
theorem debug_rx_profile :
    (execAss2 (.csrr 4 11) li64Image).ecause = 1 ∧
    (execAss2 (.csrw 4 11) li64Image).ecause = 1 ∧
    (let start := { li64Image with dbgIn := some [0x5a, 0xa5] }
     let first := execAss2 (.csrr 0 11) start
     let second := execAss2 (.csrr 4 11) first
     let empty := execAss2 (.csrr 4 11) second
     first.rget 0 = 0 ∧ first.dbgIn = some [0xa5] ∧ second.rget 4 = 0x1a5 ∧
       empty.rget 4 = 0 ∧ empty.dbgIn = some [] ∧ empty.instret = 3 ∧
       (execAss2 (.csrw 4 11) empty).ecause = 1) := by
  decide

#verify_constructive
  Qsag.Ass2.Teeth.debug_rx_profile
  Qsag.Ass2.Teeth.leaf_contract_inhabited
  Qsag.Ass2.Teeth.secretState_equiv
  Qsag.Ass2.Teeth.secretState_fetch
  Qsag.Ass2.Teeth.secretState_safe
  Qsag.Ass2.Teeth.tooth_r0_aliased_pc_turns_sel_into_secret_branch
  Qsag.Ass2.Teeth.tooth_secret_bnez_leaks_pc_trace
  Qsag.Ass2.Teeth.ass2_zero_word_traps_when_enabled
  Qsag.Ass2.Teeth.ass2_zero_word_slides_when_exc_disabled
  Qsag.Ass2.Teeth.tooth_zero_word_traps_not_nop
  Qsag.Ass2.Teeth.tooth_jalr_post_write_corrupts_self_call
  Qsag.Ass2.Teeth.dit_step_premises_inhabited
  Qsag.Ass2.Teeth.slk16_premises_inhabited

#tooth_pair Qsag.Ass2.ass2_r0_always_zero vs
  Qsag.Ass2.Teeth.tooth_r0_aliased_pc_turns_sel_into_secret_branch
#tooth_pair Qsag.Ass2.ass2_dit_step_noninterference vs
  Qsag.Ass2.Teeth.tooth_secret_bnez_leaks_pc_trace
#tooth_pair Qsag.Ass2.Teeth.ass2_zero_word_traps_when_enabled vs
  Qsag.Ass2.Teeth.tooth_zero_word_traps_not_nop
#tooth_pair Qsag.Ass2.ass2_jalr_self_alias_safe vs
  Qsag.Ass2.Teeth.tooth_jalr_post_write_corrupts_self_call

#verify_inhabited Qsag.Ass2.ass2_dit_step_noninterference
  Qsag.Ass2.Teeth.dit_step_premises_inhabited
#verify_inhabited Qsag.Ass2.ass2_slk16_four_step_loads_any_u64
  Qsag.Ass2.Teeth.slk16_premises_inhabited

end Qsag.Ass2.Teeth
