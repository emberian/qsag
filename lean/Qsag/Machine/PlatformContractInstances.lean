module
/-
# Qsag.Machine.PlatformContractInstances — platform contracts instantiated by the Machine models

`Qsag.Spec.Assumptions` states two trace-level platform contracts, `SimtWorkgroupContract` /
`WellFormedSimtContract` (GPU SIMT workgroup execution) and `DitHardwareContract`
(data-independent timing). This module builds them from the Machine-layer models.

* §1 `simtEpochContract`: the contract of one barrier epoch of a SPIR-V kernel under the Wave32
  workgroup semantics of `Machine.SpirvSimtGpuEquiv`. Its block trace, write set and read set are
  read off the observation trace `runWaveWithObs` of the kernel. Uniform control flow holds for
  every kernel of the model; disjoint storage bindings (no cell written by one invocation is
  written or read by another) are a per-kernel fact, checked for the two barrier epochs of the
  two-wave reduction kernel. The barrier-free concatenation of the two epochs is not well
  formed (`twoWaveNoBarrier_not_wellFormed`), and its output depends on the schedule
  (`twoWaveNoBarrier_schedule_dependent`).
* §2 `faial_disjointStorageBindings`: the access cells of an `EpochAccessProtocol` that satisfies
  `FaialMapRaceFree` are disjoint storage bindings.
* §3 `nttStageAddressModel` runs the decoded fused butterfly of `goldilocks_ntt.spv`
  and projects its block labels and LDS accesses. Its read set includes both twiddle planes.
* §4 `armDitContract`, `x86DitContract`: `observe` is the leakage trace of `execArmProg` /
  `execX86Prog` on a checker-accepted kernel entry; the data are the secret-labelled registers,
  flags and memory. The `ExecMode` enters through the initial `ditEnabled` / `doitEnabled` /
  `ymmUpperDirty` bits of the machine state.
* §5 `elfX86DitContract`, `elfAarch64DitContract`, `rlibX86CtEntry`, `rlibArm64CtEntry`: connects
  `Spec.DitHardwareContract` directly to `ElfVerify` and `ElfFixtureVerify`'s 28 real compiled
  `qsag-asm` `.rlib` symbol contracts (`19` `x86_64` symbols in `currentX86SymbolContracts` and `9`
  `aarch64` symbols in `currentAarch64SymbolContracts`).
-/
public import Qsag.Spec.Assumptions
public import Qsag.Machine.SpirvNttAndRlibCert
public import Qsag.Machine.SpirvSimt
public import Qsag.Machine.ConstantTimeIsa
public import Qsag.Machine.ElfFixtureVerify
import Qsag.Tactic.AssuranceKit
import Qsag.Machine.Tactic.KernelRfl

public section
namespace Qsag

set_option autoImplicit false

/-! ## §1. SIMT contract of a SPIR-V barrier epoch -/

/-- Natural-number code of a storage cell `(storage class, binding, element index)`. -/
def simtCellCode : SpirvStorageClass × Nat × Nat → Nat
  | (sc, binding, idx) => (idx * 65536 + binding) * 8 + sc.toWord.toNat

/-- The cell stored by `lane` in one observed step: the pointer of the step when the instruction
    at its program counter is `OpStore`. -/
def obsStoreCell (prog : List SpirvInst) (lane : Nat) (o : SimtWaveObs) :
    List (SpirvStorageClass × Nat × Nat) :=
  match prog[o.pc]? with
  | some (.opStore _ _) =>
    match o.memTraces[lane]? with
    | some (some c) => [c]
    | _ => []
  | _ => []

/-- Cells stored by `lane` along an observation trace. -/
def laneStoreCells (prog : List SpirvInst) (lane : Nat) (obs : List SimtWaveObs) :
    List (SpirvStorageClass × Nat × Nat) :=
  obs.flatMap (obsStoreCell prog lane)

/-- The cell loaded by `lane` in one observed step: the pointer of the step when the instruction
    at its program counter is `OpLoad`. -/
def obsLoadCell (prog : List SpirvInst) (lane : Nat) (o : SimtWaveObs) :
    List (SpirvStorageClass × Nat × Nat) :=
  match prog[o.pc]? with
  | some (.opLoad _ _ _) =>
    match o.memTraces[lane]? with
    | some (some c) => [c]
    | _ => []
  | _ => []

/-- Cells loaded by `lane` along an observation trace. -/
def laneLoadCells (prog : List SpirvInst) (lane : Nat) (obs : List SimtWaveObs) :
    List (SpirvStorageClass × Nat × Nat) :=
  obs.flatMap (obsLoadCell prog lane)

/-- Program counters of the steps in which `lane` is active. -/
def laneBlockTrace (lane : Nat) (obs : List SimtWaveObs) : List Nat :=
  (obs.filter fun o => o.activeMask.getD lane false).map (·.pc)

/-- Observation trace of wave `w` running `prog` from the initial workgroup state. -/
def waveEpochObs (env : SpirvModuleEnv) (cfg : WorkgroupConfig) (prog : List SpirvInst)
    (fuel : Nat) (mem : GpuMemState) (w : Nat) : List SimtWaveObs :=
  runWaveWithObs env prog fuel ((initWorkgroupExecState env cfg mem).waves w) mem

/-- SIMT contract of one barrier epoch: subgroups are the Wave32 waves, invocation `i` is lane
    `i % 32` of wave `i / 32`, its block trace is the program-counter trace of its active steps,
    its write set the cells of its `OpStore` steps and its read set the cells of its `OpLoad`
    steps. -/
def simtEpochContract (env : SpirvModuleEnv) (cfg : WorkgroupConfig) (prog : List SpirvInst)
    (fuel : Nat) (mem : GpuMemState) : Spec.SimtWorkgroupContract where
  subgroupSize := wave32Lanes
  workgroupSize := cfg.totalThreads
  blockTrace i :=
    laneBlockTrace (i % wave32Lanes) (waveEpochObs env cfg prog fuel mem (i / wave32Lanes))
  writeSet i :=
    (laneStoreCells prog (i % wave32Lanes)
      (waveEpochObs env cfg prog fuel mem (i / wave32Lanes))).map simtCellCode
  readSet i :=
    (laneLoadCells prog (i % wave32Lanes)
      (waveEpochObs env cfg prog fuel mem (i / wave32Lanes))).map simtCellCode
  h_divides := ⟨by rw [wave32Lanes_eq]; decide,
    ⟨cfg.numWaves, by rw [cfg.totalThreads_eq, Nat.mul_comm]⟩⟩

private theorem replicate32_getD :
    ∀ lane : Nat, lane < 32 → (List.replicate 32 true).getD lane false = true := by decide

private theorem laneBlockTrace_all_active (lane : Nat) (hl : lane < 32) :
    ∀ obs : List SimtWaveObs, (∀ o ∈ obs, o.activeMask = List.replicate 32 true) →
      laneBlockTrace lane obs = obs.map (·.pc)
  | [], _ => rfl
  | o :: rest, h => by
    have ho : o.activeMask.getD lane false = true := by
      rw [h o List.mem_cons_self]
      exact replicate32_getD lane hl
    have ih := laneBlockTrace_all_active lane hl rest
      (fun o' ho' => h o' (List.mem_cons_of_mem _ ho'))
    unfold laneBlockTrace at ih ⊢
    simp only [List.filter_cons, ho, ↓reduceIte, List.map_cons, ih]

/-- Every epoch of the Wave32 model has uniform control flow: a wave has one program counter and
    its `EXEC` mask stays fully active (`simt_ct_zero_exec_divergence`). -/
theorem simtEpochContract_uniformControlFlow (env : SpirvModuleEnv) (cfg : WorkgroupConfig)
    (prog : List SpirvInst) (fuel : Nat) (mem : GpuMemState) :
    (simtEpochContract env cfg prog fuel mem).UniformControlFlow := by
  intro i j _ _ hij
  have hij' : i / wave32Lanes = j / wave32Lanes := hij
  show laneBlockTrace (i % wave32Lanes) (waveEpochObs env cfg prog fuel mem (i / wave32Lanes)) =
    laneBlockTrace (j % wave32Lanes) (waveEpochObs env cfg prog fuel mem (j / wave32Lanes))
  rw [hij']
  have hAll : ∀ o ∈ waveEpochObs env cfg prog fuel mem (j / wave32Lanes),
      o.activeMask = List.replicate 32 true :=
    fun o ho => simt_ct_zero_exec_divergence env prog fuel _ mem
      (by rw [initWorkgroupExecState.public_eq_1]) o ho
  have hLane : ∀ k : Nat, k % wave32Lanes < 32 := fun k => by
    rw [wave32Lanes_eq]
    exact Nat.mod_lt k (by decide)
  rw [laneBlockTrace_all_active _ (hLane i) _ hAll, laneBlockTrace_all_active _ (hLane j) _ hAll]

/-- For a kernel accepted by `checkProgSimtCt`, the block traces and write sets of the contract
    do not depend on the secret-labelled memory contents. -/
theorem simtEpochContract_memory_independent {env : SpirvModuleEnv} {pol : SimtCtPolicy}
    {prog : List SpirvInst} (hScalar : ScalarConstEnv env)
    (hCt : checkProgSimtCt env pol prog = true) (cfg : WorkgroupConfig) (fuel : Nat)
    {m₁ m₂ : GpuMemState} (hMem : MemLowEq pol m₁ m₂) :
    (simtEpochContract env cfg prog fuel m₁).blockTrace =
      (simtEpochContract env cfg prog fuel m₂).blockTrace ∧
    (simtEpochContract env cfg prog fuel m₁).writeSet =
      (simtEpochContract env cfg prog fuel m₂).writeSet := by
  have hObs : ∀ w : Nat, waveEpochObs env cfg prog fuel m₁ w = waveEpochObs env cfg prog fuel m₂ w :=
    fun w => by
      unfold waveEpochObs
      rw [initWorkgroupExecState.public_eq_1, initWorkgroupExecState.public_eq_1]
      exact simt_ct_noninterference hCt fuel (initWave_lowEq env pol cfg hScalar w) hMem
  constructor
  · funext i
    show laneBlockTrace _ (waveEpochObs env cfg prog fuel m₁ _) =
      laneBlockTrace _ (waveEpochObs env cfg prog fuel m₂ _)
    rw [hObs]
  · funext i
    show (laneStoreCells prog _ (waveEpochObs env cfg prog fuel m₁ _)).map simtCellCode =
      (laneStoreCells prog _ (waveEpochObs env cfg prog fuel m₂ _)).map simtCellCode
    rw [hObs]

/-- Executable check of an epoch against a set `writable` of cell codes and a map `owner`:
    every cell stored by an invocation is writable and owned by it, and every cell loaded by an
    invocation is either not writable or owned by it. -/
def simtEpochOwnerCheck (env : SpirvModuleEnv) (cfg : WorkgroupConfig) (prog : List SpirvInst)
    (fuel : Nat) (mem : GpuMemState) (writable : Nat → Bool) (owner : Nat → Nat) : Bool :=
  (List.range cfg.numWaves).all fun w =>
    (waveEpochObs env cfg prog fuel mem w).all fun o =>
      (List.range wave32Lanes).all fun lane =>
        (obsStoreCell prog lane o).all (fun c =>
          writable (simtCellCode c) && owner (simtCellCode c) == w * wave32Lanes + lane) &&
        (obsLoadCell prog lane o).all (fun c =>
          !writable (simtCellCode c) || owner (simtCellCode c) == w * wave32Lanes + lane)

/-- A kernel epoch that passes the owner check has a well-formed contract: a cell stored by an
    invocation is neither stored nor loaded by another. -/
theorem simtEpochContract_wellFormed_of_ownerCheck {env : SpirvModuleEnv} {cfg : WorkgroupConfig}
    {prog : List SpirvInst} {fuel : Nat} {mem : GpuMemState} {writable : Nat → Bool}
    {owner : Nat → Nat}
    (hCheck : simtEpochOwnerCheck env cfg prog fuel mem writable owner = true) :
    Spec.WellFormedSimtContract (simtEpochContract env cfg prog fuel mem) := by
  have hLane : ∀ i : Nat, i < cfg.totalThreads →
      ∀ o ∈ waveEpochObs env cfg prog fuel mem (i / wave32Lanes),
        ((obsStoreCell prog (i % wave32Lanes) o).all (fun c =>
          writable (simtCellCode c) && owner (simtCellCode c) == i) &&
        (obsLoadCell prog (i % wave32Lanes) o).all (fun c =>
          !writable (simtCellCode c) || owner (simtCellCode c) == i)) = true := by
    intro i hi o ho
    have hw : i / wave32Lanes < cfg.numWaves := by
      have h32 : i / 32 < cfg.numWaves := by
        have hi32 := hi
        rw [cfg.totalThreads_eq, wave32Lanes_eq] at hi32
        omega
      rw [wave32Lanes_eq]
      exact h32
    have hl : i % wave32Lanes < wave32Lanes := Nat.mod_lt i (by rw [wave32Lanes_eq]; decide)
    have h1 := List.all_eq_true.mp hCheck (i / wave32Lanes) (List.mem_range.mpr hw)
    have h2 := List.all_eq_true.mp h1 o ho
    have h3 := List.all_eq_true.mp h2 (i % wave32Lanes) (List.mem_range.mpr hl)
    have hI : i / wave32Lanes * wave32Lanes + i % wave32Lanes = i := by
      rw [Nat.mul_comm]
      exact Nat.div_add_mod i wave32Lanes
    rw [hI] at h3
    exact h3
  have hOwn : ∀ i : Nat, i < cfg.totalThreads →
      ∀ cell ∈ (simtEpochContract env cfg prog fuel mem).writeSet i,
        writable cell = true ∧ owner cell = i := by
    intro i hi cell hCell
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hCell
    obtain ⟨o, ho, hco⟩ := List.mem_flatMap.mp hc
    have h4 := List.all_eq_true.mp (Bool.and_eq_true_iff.mp (hLane i hi o ho)).1 c hco
    exact ⟨(Bool.and_eq_true_iff.mp h4).1, Nat.eq_of_beq_eq_true (Bool.and_eq_true_iff.mp h4).2⟩
  have hRead : ∀ j : Nat, j < cfg.totalThreads →
      ∀ cell ∈ (simtEpochContract env cfg prog fuel mem).readSet j,
        writable cell = true → owner cell = j := by
    intro j hj cell hCell hWr
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hCell
    obtain ⟨o, ho, hco⟩ := List.mem_flatMap.mp hc
    have h4 := List.all_eq_true.mp (Bool.and_eq_true_iff.mp (hLane j hj o ho)).2 c hco
    rw [hWr] at h4
    exact Nat.eq_of_beq_eq_true h4
  exact ⟨(simtEpochContract env cfg prog fuel mem).h_divides,
    simtEpochContract_uniformControlFlow env cfg prog fuel mem,
    fun i j hi hj hne cell hci =>
      ⟨fun hcj => hne ((hOwn i hi cell hci).2.symm.trans (hOwn j hj cell hcj).2),
       fun hcj => hne ((hOwn i hi cell hci).2.symm.trans
         (hRead j hj cell hcj (hOwn i hi cell hci).1))⟩⟩

/-! ### The two-wave reduction kernel (`LocalSize 64`, two Wave32 subgroups) -/

/-- Element index of a storage cell code. -/
def simtCellIndex (cell : Nat) : Nat := cell / 8 / 65536

/-- The two barrier-separated epochs of the reduction kernel concatenated into one epoch. -/
def twoWaveNoBarrierEpoch : List SpirvInst := twoWavePhase0WriteLds ++ twoWavePhase1CrossWaveRead

/-- Cell codes of the LDS words (`Workgroup`, binding `0`): the cells the first epoch stores. -/
def twoWaveLdsCell (cell : Nat) : Bool := cell % 524288 == 4

/-- Cell codes of the output buffer words: the cells the second epoch stores. -/
def twoWaveOutCell (cell : Nat) : Bool := cell % 524288 == 20

theorem twoWaveCfg_totalThreads : twoWaveCfg.totalThreads = 64 := by
  have h := twoWaveCfg.totalThreads_eq
  rw [twoWaveCfg_numWaves, wave32Lanes_eq] at h
  exact h

theorem twoWavePhase0_ownerCheck (mem : GpuMemState) :
    simtEpochOwnerCheck twoWaveReductionEnv twoWaveCfg twoWavePhase0WriteLds 4 mem twoWaveLdsCell
      simtCellIndex = true := by
  simp only [simtEpochOwnerCheck, waveEpochObs, twoWaveCfg_numWaves, wave32Lanes_eq,
    show List.range 2 = [0, 1] from rfl, List.all_cons, List.all_nil, Bool.and_true,
    twoWavePhase0_waveObs mem 0 (by decide), twoWavePhase0_waveObs mem 1 (by decide)]
  rw [twoWavePhase0WriteLds.public_eq_1]
  decide +kernel

theorem twoWavePhase1_ownerCheck (mem : GpuMemState) :
    simtEpochOwnerCheck twoWaveReductionEnv twoWaveCfg twoWavePhase1CrossWaveRead 8 mem
      twoWaveOutCell simtCellIndex = true := by
  simp only [simtEpochOwnerCheck, waveEpochObs, twoWaveCfg_numWaves, wave32Lanes_eq,
    show List.range 2 = [0, 1] from rfl, List.all_cons, List.all_nil, Bool.and_true,
    twoWavePhase1_waveObs mem 0 (by decide), twoWavePhase1_waveObs mem 1 (by decide)]
  rw [twoWavePhase1CrossWaveRead.public_eq_1]
  decide +kernel

private theorem mem_writeSet_of_mem {env : SpirvModuleEnv} {cfg : WorkgroupConfig}
    {prog : List SpirvInst} {fuel : Nat} {mem : GpuMemState} {i : Nat}
    {c : SpirvStorageClass × Nat × Nat}
    (h : c ∈ laneStoreCells prog (i % 32) (waveEpochObs env cfg prog fuel mem (i / 32))) :
    simtCellCode c ∈ (simtEpochContract env cfg prog fuel mem).writeSet i := by
  show simtCellCode c ∈ (laneStoreCells prog (i % wave32Lanes)
    (waveEpochObs env cfg prog fuel mem (i / wave32Lanes))).map simtCellCode
  rw [wave32Lanes_eq]
  exact List.mem_map_of_mem h

private theorem twoWave_lt_workgroupSize {prog : List SpirvInst} {fuel : Nat} {mem : GpuMemState}
    {i : Nat} (hi : i < 64) :
    i < (simtEpochContract twoWaveReductionEnv twoWaveCfg prog fuel mem).workgroupSize := by
  show i < twoWaveCfg.totalThreads
  rw [twoWaveCfg_totalThreads]
  exact hi

/-- Both barrier epochs of the reduction kernel satisfy the SIMT contract on every memory:
    invocation `tid` stores `lds[tid]` in the first epoch and `outBuf[tid]` in the second; the
    second epoch loads `lds[tid]` and `lds[tid ^ 32]`, which no invocation stores in that
    epoch. -/
theorem twoWaveReduction_epochs_wellFormed (mem : GpuMemState) :
    Spec.WellFormedSimtContract
      (simtEpochContract twoWaveReductionEnv twoWaveCfg twoWavePhase0WriteLds 4 mem) ∧
    Spec.WellFormedSimtContract
      (simtEpochContract twoWaveReductionEnv twoWaveCfg twoWavePhase1CrossWaveRead 8 mem) :=
  ⟨simtEpochContract_wellFormed_of_ownerCheck (twoWavePhase0_ownerCheck mem),
   simtEpochContract_wellFormed_of_ownerCheck (twoWavePhase1_ownerCheck mem)⟩

/-- Write-race freedom of the reduction kernel: a storage cell stored during an epoch has one
    storing invocation among the `64`. -/
theorem twoWaveReduction_write_race_free (mem : GpuMemState) (i j : Nat) (hi : i < 64)
    (hj : j < 64) (c : SpirvStorageClass × Nat × Nat) :
    (c ∈ laneStoreCells twoWavePhase0WriteLds (i % 32)
          (waveEpochObs twoWaveReductionEnv twoWaveCfg twoWavePhase0WriteLds 4 mem (i / 32)) →
      c ∈ laneStoreCells twoWavePhase0WriteLds (j % 32)
          (waveEpochObs twoWaveReductionEnv twoWaveCfg twoWavePhase0WriteLds 4 mem (j / 32)) →
      i = j) ∧
    (c ∈ laneStoreCells twoWavePhase1CrossWaveRead (i % 32)
          (waveEpochObs twoWaveReductionEnv twoWaveCfg twoWavePhase1CrossWaveRead 8 mem (i / 32)) →
      c ∈ laneStoreCells twoWavePhase1CrossWaveRead (j % 32)
          (waveEpochObs twoWaveReductionEnv twoWaveCfg twoWavePhase1CrossWaveRead 8 mem (j / 32)) →
      i = j) :=
  ⟨fun hci hcj => (twoWaveReduction_epochs_wellFormed mem).1.write_race_free i j (simtCellCode c)
      (twoWave_lt_workgroupSize hi) (twoWave_lt_workgroupSize hj) (mem_writeSet_of_mem hci)
      (mem_writeSet_of_mem hcj),
   fun hci hcj => (twoWaveReduction_epochs_wellFormed mem).2.write_race_free i j (simtCellCode c)
      (twoWave_lt_workgroupSize hi) (twoWave_lt_workgroupSize hj) (mem_writeSet_of_mem hci)
      (mem_writeSet_of_mem hcj)⟩

/-- Secret-data policy of the first reduction epoch: the loaded word `%11`, the input buffer and
    the LDS are secret; pointers and indices are public. -/
def twoWaveSecretDataPolicy : SimtCtPolicy where
  ssboSec _ := .sec
  ldsSec := .sec
  regSec id := if id == 11 then .sec else .pub

/-- The contract of the first reduction epoch is the same for all LDS and storage-buffer
    contents. -/
theorem twoWavePhase0_contract_memory_independent (m₁ m₂ : GpuMemState)
    (hPush : m₁.pushConsts = m₂.pushConsts) :
    (simtEpochContract twoWaveReductionEnv twoWaveCfg twoWavePhase0WriteLds 4 m₁).blockTrace =
      (simtEpochContract twoWaveReductionEnv twoWaveCfg twoWavePhase0WriteLds 4 m₂).blockTrace ∧
    (simtEpochContract twoWaveReductionEnv twoWaveCfg twoWavePhase0WriteLds 4 m₁).writeSet =
      (simtEpochContract twoWaveReductionEnv twoWaveCfg twoWavePhase0WriteLds 4 m₂).writeSet := by
  exact simtEpochContract_memory_independent (pol := twoWaveSecretDataPolicy)
    twoWaveReductionEnv_scalarConst twoWavePhase0_simtCt_secretData twoWaveCfg 4
    (by rw [MemLowEq.public_eq_1]
        exact ⟨hPush, fun h => SecLabel.noConfusion h, fun _ h => SecLabel.noConfusion h⟩)

/-- Secret-data policy of the second reduction epoch: the loaded words `%14` and `%17`, their sum
    `%18`, the storage buffers and the LDS are secret; pointers and indices are public. -/
def twoWavePhase1SecretDataPolicy : SimtCtPolicy where
  ssboSec _ := .sec
  ldsSec := .sec
  regSec id := if id == 14 || id == 17 || id == 18 then .sec else .pub

/-- The second reduction epoch is accepted by the `SIMT-CT` checker under the secret-data policy:
    its access chain `%19 = &outBuf[tid]` is typed with pointer type `%9`, which
    `twoWaveReductionEnv.ptrInfo` binds to storage buffer `1` like `%4` and `%19`. -/
theorem twoWavePhase1_accepted_by_simtCt :
    checkProgSimtCt twoWaveReductionEnv twoWavePhase1SecretDataPolicy
      twoWavePhase1CrossWaveRead = true :=
  twoWavePhase1_simtCt_secretData

/-- The contract of the second reduction epoch is the same for all LDS and storage-buffer
    contents. -/
theorem twoWavePhase1_contract_memory_independent (m₁ m₂ : GpuMemState)
    (hPush : m₁.pushConsts = m₂.pushConsts) :
    (simtEpochContract twoWaveReductionEnv twoWaveCfg twoWavePhase1CrossWaveRead 8 m₁).blockTrace =
      (simtEpochContract twoWaveReductionEnv twoWaveCfg twoWavePhase1CrossWaveRead 8
        m₂).blockTrace ∧
    (simtEpochContract twoWaveReductionEnv twoWaveCfg twoWavePhase1CrossWaveRead 8 m₁).writeSet =
      (simtEpochContract twoWaveReductionEnv twoWaveCfg twoWavePhase1CrossWaveRead 8
        m₂).writeSet := by
  exact simtEpochContract_memory_independent (pol := twoWavePhase1SecretDataPolicy)
    twoWaveReductionEnv_scalarConst twoWavePhase1_accepted_by_simtCt twoWaveCfg 8
    (by rw [MemLowEq.public_eq_1]
        exact ⟨hPush, fun h => SecLabel.noConfusion h, fun _ h => SecLabel.noConfusion h⟩)

/-- A kernel whose output access chain `%19 = &outBuf[tid]` is typed with the input-buffer
    pointer type `%7` is rejected by the `SIMT-CT` checker under every policy:
    `twoWaveReductionEnv.ptrInfo` binds `%7` to storage buffer `0` while `%4` and `%19` are bound
    to storage buffer `1`. `simt_ct_noninterference` does not apply to such a kernel. -/
theorem twoWave_mistyped_output_rejected_by_simtCt (pol : SimtCtPolicy)
    (pre post : List SpirvInst) :
    checkProgSimtCt twoWaveReductionEnv pol (pre ++ .opAccessChain 7 19 4 [1] :: post) = false := by
  rw [checkProgSimtCt.public_eq_1, List.all_append, List.all_cons,
    twoWaveReductionEnv_mistyped_output_accessChain_rejected, Bool.false_and, Bool.and_false]

theorem twoWaveNoBarrier_cross_wave_cell (mem : GpuMemState) :
    List.elem 16777220
        ((simtEpochContract twoWaveReductionEnv twoWaveCfg twoWaveNoBarrierEpoch 12 mem).writeSet
          32) = true ∧
      List.elem 16777220
        ((simtEpochContract twoWaveReductionEnv twoWaveCfg twoWaveNoBarrierEpoch 12 mem).readSet
          0) = true := by
  constructor
  · simp only [simtEpochContract, waveEpochObs, twoWaveNoBarrierEpoch, wave32Lanes_eq,
      Nat.reduceDiv, twoWaveNoBarrier_waveObs mem 1 (by decide)]
    rw [twoWavePhase0WriteLds.public_eq_1, twoWavePhase1CrossWaveRead.public_eq_1]
    decide +kernel
  · simp only [simtEpochContract, waveEpochObs, twoWaveNoBarrierEpoch, wave32Lanes_eq,
      Nat.reduceDiv, twoWaveNoBarrier_waveObs mem 0 (by decide)]
    rw [twoWavePhase0WriteLds.public_eq_1, twoWavePhase1CrossWaveRead.public_eq_1]
    decide +kernel

/-- **The barrier-free concatenation of the two reduction epochs is not well formed**, on any
    memory: invocation `32` stores `lds[32]` and invocation `0` loads it in the same epoch. The
    barrier between the two epochs is what makes each of them race free. -/
theorem twoWaveNoBarrier_not_wellFormed (mem : GpuMemState) :
    ¬ Spec.WellFormedSimtContract
      (simtEpochContract twoWaveReductionEnv twoWaveCfg twoWaveNoBarrierEpoch 12 mem) := by
  intro w
  have hi : 32 < (simtEpochContract twoWaveReductionEnv twoWaveCfg twoWaveNoBarrierEpoch 12
      mem).workgroupSize := twoWave_lt_workgroupSize (by decide)
  have hj : 0 < (simtEpochContract twoWaveReductionEnv twoWaveCfg twoWaveNoBarrierEpoch 12
      mem).workgroupSize := twoWave_lt_workgroupSize (by decide)
  have h := w.read_write_race_free 32 0 16777220 hi hj
    (List.mem_of_elem_eq_true (twoWaveNoBarrier_cross_wave_cell mem).1)
    (List.mem_of_elem_eq_true (twoWaveNoBarrier_cross_wave_cell mem).2)
  exact absurd h (by decide)

/-- The race is observable: two schedules of the barrier-free epoch write different values to
    `outBuf[0]`. -/
theorem twoWaveNoBarrier_schedule_dependent :
    ∃ (mem : GpuMemState) (s₁ s₂ : List Nat),
      ¬ (peekSsboDword 1 0 (runInterleavedSchedule twoWaveReductionEnv twoWaveCfg
            twoWaveNoBarrierEpoch s₁ (initWorkgroupExecState twoWaveReductionEnv twoWaveCfg mem)) =
         peekSsboDword 1 0 (runInterleavedSchedule twoWaveReductionEnv twoWaveCfg
            twoWaveNoBarrierEpoch s₂ (initWorkgroupExecState twoWaveReductionEnv twoWaveCfg mem))) :=
  tooth_missing_barrier_causes_cross_wave_lds_race

/-! ## §2. Access protocols -/

/-- Write cells of thread `t` under an access protocol, inside the address window
    `ldsLen` LDS dwords and `bindings × ssboLen` storage-buffer dwords. -/
def protocolWriteCells (proto : EpochAccessProtocol) (ldsLen bindings ssboLen t : Nat) :
    List Nat :=
  ((List.range ldsLen).filter (proto.ldsWrite t)).map (fun a => 2 * a) ++
  ((List.range (bindings * ssboLen)).filter
    (fun k => proto.ssboWrite t (k % bindings) (k / bindings))).map (fun k => 2 * k + 1)

/-- Read cells of thread `t` under an access protocol, inside the same address window. -/
def protocolReadCells (proto : EpochAccessProtocol) (ldsLen bindings ssboLen t : Nat) :
    List Nat :=
  ((List.range ldsLen).filter (proto.ldsRead t)).map (fun a => 2 * a) ++
  ((List.range (bindings * ssboLen)).filter
    (fun k => proto.ssboRead t (k % bindings) (k / bindings))).map (fun k => 2 * k + 1)

/-- SIMT contract of an access protocol over a workgroup configuration. -/
def protocolSimtContract (cfg : WorkgroupConfig) (proto : EpochAccessProtocol)
    (ldsLen bindings ssboLen : Nat) (blockTrace : Nat → List Nat) : Spec.SimtWorkgroupContract where
  subgroupSize := wave32Lanes
  workgroupSize := cfg.totalThreads
  blockTrace := blockTrace
  writeSet := protocolWriteCells proto ldsLen bindings ssboLen
  readSet := protocolReadCells proto ldsLen bindings ssboLen
  h_divides := ⟨by rw [wave32Lanes_eq]; decide,
    ⟨cfg.numWaves, by rw [cfg.totalThreads_eq, Nat.mul_comm]⟩⟩

/-- `FaialMapRaceFree`, the hypothesis of `multiWave_schedule_confluence`, gives the
    disjoint-storage-bindings field of the SIMT contract: no cell written by a thread is
    written or read by another. -/
theorem faial_disjointStorageBindings {cfg : WorkgroupConfig} {proto : EpochAccessProtocol}
    (hDrf : FaialMapRaceFree cfg.totalThreads proto) (ldsLen bindings ssboLen : Nat)
    (blockTrace : Nat → List Nat) :
    (protocolSimtContract cfg proto ldsLen bindings ssboLen blockTrace).DisjointStorageBindings := by
  intro i j hi hj hne cell hci
  rw [FaialMapRaceFree.public_eq_1] at hDrf
  have hF := hDrf i j hi hj hne
  have hKey : ∀ (wr rd : Nat → Nat → Bool) (wr2 rd2 : Nat → Nat → Nat → Bool),
      (∀ a : Nat, wr i a = true → wr j a = false ∧ rd j a = false) →
      (∀ b a : Nat, wr2 i b a = true → wr2 j b a = false ∧ rd2 j b a = false) →
      cell ∈ ((List.range ldsLen).filter (wr i)).map (fun a => 2 * a) ++
        ((List.range (bindings * ssboLen)).filter
          (fun k => wr2 i (k % bindings) (k / bindings))).map (fun k => 2 * k + 1) →
      ∀ (f : Nat → Nat → Bool) (f2 : Nat → Nat → Nat → Bool),
        (∀ a : Nat, wr i a = true → f j a = false) →
        (∀ b a : Nat, wr2 i b a = true → f2 j b a = false) →
        cell ∉ ((List.range ldsLen).filter (f j)).map (fun a => 2 * a) ++
          ((List.range (bindings * ssboLen)).filter
            (fun k => f2 j (k % bindings) (k / bindings))).map (fun k => 2 * k + 1) := by
    intro wr rd wr2 rd2 _ _ hci f f2 hf hf2 hcj
    rcases List.mem_append.mp hci with h1 | h1 <;> rcases List.mem_append.mp hcj with h2 | h2
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp h1
      obtain ⟨b, hb, hEq⟩ := List.mem_map.mp h2
      have hab : b = a := by omega
      subst hab
      have hj' := hf b (List.mem_filter.mp ha).2
      rw [(List.mem_filter.mp hb).2] at hj'
      cases hj'
    · obtain ⟨a, _, rfl⟩ := List.mem_map.mp h1
      obtain ⟨b, _, hEq⟩ := List.mem_map.mp h2
      omega
    · obtain ⟨a, _, rfl⟩ := List.mem_map.mp h1
      obtain ⟨b, _, hEq⟩ := List.mem_map.mp h2
      omega
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp h1
      obtain ⟨b, hb, hEq⟩ := List.mem_map.mp h2
      have hab : b = a := by omega
      subst hab
      have hj' := hf2 _ _ (List.mem_filter.mp ha).2
      rw [(List.mem_filter.mp hb).2] at hj'
      cases hj'
  exact ⟨hKey proto.ldsWrite proto.ldsRead proto.ssboWrite proto.ssboRead hF.1 hF.2 hci
      proto.ldsWrite proto.ssboWrite (fun a h => (hF.1 a h).1) (fun b a h => (hF.2 b a h).1),
    hKey proto.ldsWrite proto.ldsRead proto.ssboWrite proto.ssboRead hF.1 hF.2 hci
      proto.ldsRead proto.ssboRead (fun a h => (hF.1 a h).2) (fun b a h => (hF.2 b a h).2)⟩

/-! ## §3. Decoded SPIR-V execution of one fused NTT stage of `goldilocks_ntt.comp` -/

/-- Workgroup geometry of `goldilocks_ntt.comp`: `local_size_x = 256`, eight Wave32 subgroups. -/
def productionNttCfg : WorkgroupConfig :=
  { workgroupId := 0, numWaves := 8, wavesPos := by decide, workgroupCount := 1 }

/-- LDS cells stored by invocation `lid` in fused stage `stage`: both butterfly outputs, in the
    low-word plane `s_lds[0]` and the high-word plane `s_lds[1]` (offset `512`). -/
def productionNttStageWrites (stage lid : Nat) : List Nat :=
  [ productionLdsIndex (productionButterflyIndex stage (lid / 32) 0 (lid % 32)),
    productionLdsIndex (productionButterflyIndex stage (lid / 32) 1 (lid % 32)),
    512 + productionLdsIndex (productionButterflyIndex stage (lid / 32) 0 (lid % 32)),
    512 + productionLdsIndex (productionButterflyIndex stage (lid / 32) 1 (lid % 32)) ]

/-- The invocation storing an LDS cell in fused stage `stage`. -/
def productionNttWriter (stage cell : Nat) : Nat :=
  ((productionLdsIndex (cell % 512) >>> (stage + 1)) <<< stage) +
    (productionLdsIndex (cell % 512) &&& (2 ^ stage - 1))

/-- Operational contract for one zero-based fused NTT stage. -/
def nttStageAddressModel (stage : Nat) : Spec.SimtWorkgroupContract :=
  Spv.decodedStageContract stage

theorem nttStageAddressModel_disjointStorageBindings (stage : Fin 9) :
    (nttStageAddressModel stage).DisjointStorageBindings :=
  Spv.ntt_decoded_stage_disjoint stage

theorem nttStageAddressModel_nonempty (stage : Fin 9) (lid : Nat) :
    (nttStageAddressModel stage).blockTrace lid ≠ [] :=
  Spv.ntt_decoded_stage_nonempty stage lid

end Qsag

/-! ## §4. Data-independent timing contract of the constant-time ISA models -/

namespace Qsag.ConstantTimeIsa

/-- A kernel entry accepted by the `aarch64` constant-time checker, with the public part of its
    entry state. -/
structure ArmCtEntry where
  prog : List ArmStmt
  τ : ArmTaintState
  memPol : BitVec 64 → SecLabel
  secHeap : Bool
  hPol : secHeap = true → ∀ a, memPol a = .sec
  hCheck : (checkArmProg secHeap τ prog).isSome = true
  pub : ArmState

/-- Entry state: public-labelled components from the entry, secret-labelled components from the
    data, `PSTATE.DIT` from the execution mode. -/
def ArmCtEntry.entryState (e : ArmCtEntry) (mode : Spec.ExecMode) (sec : ArmState) : ArmState where
  gpr r := if e.τ.gpr r = .pub then e.pub.gpr r else sec.gpr r
  neon v := if e.τ.neon v = .pub then e.pub.neon v else sec.neon v
  flags :=
    { z := if e.τ.z = .pub then e.pub.flags.z else sec.flags.z
      c := if e.τ.c = .pub then e.pub.flags.c else sec.flags.c }
  mem a := if e.memPol a = .pub then e.pub.mem a else sec.mem a
  ditEnabled := mode.ditEnabled

/-- Leakage trace of the `aarch64` model on a kernel entry. -/
def armLeakage (mode : Spec.ExecMode) (e : ArmCtEntry) (sec : ArmState) : List LeakageEvent :=
  (execArmProg e.prog 0 (e.entryState mode sec)).2

theorem ArmCtEntry.entryState_lowEq (e : ArmCtEntry) (d₁ d₂ : ArmState) :
    ArmLowEq e.memPol e.τ (e.entryState Spec.ExecMode.constantTimeSafe d₁)
      (e.entryState Spec.ExecMode.constantTimeSafe d₂) := by
  refine ⟨fun r h => ?_, fun v h => ?_, fun h => ?_, fun h => ?_, fun a h => ?_, rfl, fun _ => rfl⟩
  all_goals simp only [ArmCtEntry.entryState, h, ↓reduceIte]

/-- The `aarch64` leakage model satisfies the data-independent-timing contract on
    checker-accepted kernel entries (`arm_ct_checker_sound`). -/
def armDitContract : Spec.DitHardwareContract ArmCtEntry ArmState (List LeakageEvent) where
  observe := armLeakage
  dataIndependent e d₁ d₂ := by
    obtain ⟨τOut, hOut⟩ := Option.isSome_iff_exists.mp e.hCheck
    exact (arm_ct_checker_sound e.memPol e.secHeap e.hPol e.prog e.τ τOut 0 hOut _ _
      (e.entryState_lowEq d₁ d₂)).1

/-- A kernel entry accepted by the `x86_64` constant-time checker. -/
structure X86CtEntry where
  prog : List X86Stmt
  τ : X86TaintState
  memPol : BitVec 64 → SecLabel
  secHeap : Bool
  hPol : secHeap = true → ∀ a, memPol a = .sec
  hCheck : (checkX86Prog secHeap τ prog).isSome = true
  pub : X86State

/-- Entry state: `DOITM` from `mode.ditEnabled`, upper-YMM dirtiness from `mode.cleanSimdUpper`. -/
def X86CtEntry.entryState (e : X86CtEntry) (mode : Spec.ExecMode) (sec : X86State) : X86State where
  gpr r := if e.τ.gpr r = .pub then e.pub.gpr r else sec.gpr r
  ymm y := if e.τ.ymm y = .pub then e.pub.ymm y else sec.ymm y
  flags :=
    { cf := if e.τ.cf = .pub then e.pub.flags.cf else sec.flags.cf
      of := if e.τ.of = .pub then e.pub.flags.of else sec.flags.of
      zf := if e.τ.zf = .pub then e.pub.flags.zf else sec.flags.zf }
  mem a := if e.memPol a = .pub then e.pub.mem a else sec.mem a
  doitEnabled := mode.ditEnabled
  ymmUpperDirty := !mode.cleanSimdUpper

/-- Leakage trace of the `x86_64` model on a kernel entry. -/
def x86Leakage (mode : Spec.ExecMode) (e : X86CtEntry) (sec : X86State) : List LeakageEvent :=
  (execX86Prog e.prog 0 (e.entryState mode sec)).2

theorem X86CtEntry.entryState_lowEq (e : X86CtEntry) (d₁ d₂ : X86State) :
    X86LowEq e.memPol e.τ (e.entryState Spec.ExecMode.constantTimeSafe d₁)
      (e.entryState Spec.ExecMode.constantTimeSafe d₂) := by
  refine ⟨fun r h => ?_, fun y h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun a h => ?_,
    rfl, fun _ => rfl, rfl, fun _ => rfl⟩
  all_goals simp only [X86CtEntry.entryState, h, ↓reduceIte]

/-- The `x86_64` leakage model satisfies the data-independent-timing contract on
    checker-accepted kernel entries (`x86_ct_checker_sound`). -/
def x86DitContract : Spec.DitHardwareContract X86CtEntry X86State (List LeakageEvent) where
  observe := x86Leakage
  dataIndependent e d₁ d₂ := by
    obtain ⟨τOut, hOut⟩ := Option.isSome_iff_exists.mp e.hCheck
    exact (x86_ct_checker_sound e.memPol e.secHeap e.hPol e.prog e.τ τOut 0 hOut _ _
      (e.entryState_lowEq d₁ d₂)).1

/-! ### A checker-accepted entry

`Machine.ConstantTimeIsa` models no `qsag-asm` kernel in its hand-written AST (the kernels are
proved on their decoded bytes in `Machine.McRefine`, `Machine.ElfFunctionalEquiv` and
`Machine.SydTv`). The entry below is the fragment `umulh x2, x0, x1; ret`, whose timing depends
on `DIT`. -/

def umulhArmEntry (pub : ArmState) : ArmCtEntry :=
  { prog := [.instr (.umulh64 .x2 .x0 .x1), .ret], τ := glAllSecretArmTaint,
    memPol := fun _ => .sec, secHeap := true, hPol := fun _ _ => rfl,
    hCheck := umulhArmProg_checked, pub := pub }

/-- State with operands `a`, `b` in `x0`, `x1`. -/
def umulhArmState (a b : BitVec 64) : ArmState :=
  { gpr := fun r => if r == .x0 then a else if r == .x1 then b else 0#64
    neon := fun _ => Vec128.zero
    flags := { z := false, c := false }
    mem := fun _ => 0#64
    ditEnabled := false }

/-- Any sequence of `aarch64` kernel invocations with the same entries leaks the same traces,
    whatever the secret-labelled data. -/
theorem arm_kernel_sequence_leakage_data_independent
    (tr₁ tr₂ : List (ArmCtEntry × ArmState)) (h : tr₁.map Prod.fst = tr₂.map Prod.fst) :
    tr₁.map (fun e => armLeakage Spec.ExecMode.constantTimeSafe e.1 e.2) =
      tr₂.map (fun e => armLeakage Spec.ExecMode.constantTimeSafe e.1 e.2) :=
  armDitContract.trace_data_independent Spec.ExecMode.constantTimeSafe rfl tr₁ tr₂ h

/-- Any sequence of `x86_64` kernel invocations with the same entries leaks the same traces,
    whatever the secret-labelled data. -/
theorem x86_kernel_sequence_leakage_data_independent
    (tr₁ tr₂ : List (X86CtEntry × X86State)) (h : tr₁.map Prod.fst = tr₂.map Prod.fst) :
    tr₁.map (fun e => x86Leakage Spec.ExecMode.constantTimeSafe e.1 e.2) =
      tr₂.map (fun e => x86Leakage Spec.ExecMode.constantTimeSafe e.1 e.2) :=
  x86DitContract.trace_data_independent Spec.ExecMode.constantTimeSafe rfl tr₁ tr₂ h

/-- The contract has kernel sequences with differing secret operands and equal leakage. -/
theorem inhabited_arm_kernel_sequence :
    ∃ tr₁ tr₂ : List (ArmCtEntry × ArmState),
      tr₁.map Prod.fst = tr₂.map Prod.fst ∧
      ¬ (tr₁.map (fun e => e.2.gpr .x0) = tr₂.map (fun e => e.2.gpr .x0)) ∧
      tr₁.map (fun e => armLeakage Spec.ExecMode.constantTimeSafe e.1 e.2) =
        tr₂.map (fun e => armLeakage Spec.ExecMode.constantTimeSafe e.1 e.2) :=
  ⟨[(umulhArmEntry (umulhArmState 0#64 0#64), umulhArmState 3#64 5#64)],
   [(umulhArmEntry (umulhArmState 0#64 0#64), umulhArmState 7#64 5#64)], rfl, by decide,
   arm_kernel_sequence_leakage_data_independent _ _ rfl⟩

/-- `#tooth`: the mode bit is needed. With `ditEnabled = false` the `umulh` entry leaks its
    operand. -/
theorem tooth_arm_umulh_leaks_without_dit_mode :
    ¬ (armLeakage { Spec.ExecMode.constantTimeSafe with ditEnabled := false }
          (umulhArmEntry (umulhArmState 0#64 0#64)) (umulhArmState 3#64 5#64) =
       armLeakage { Spec.ExecMode.constantTimeSafe with ditEnabled := false }
          (umulhArmEntry (umulhArmState 0#64 0#64)) (umulhArmState 7#64 5#64)) := by
  refine umulhArmProg_leaks_without_dit _ _ rfl rfl ?_
  show ¬ ((if glAllSecretArmTaint.gpr .x0 = .pub then (umulhArmState 0#64 0#64).gpr .x0
      else (umulhArmState 3#64 5#64).gpr .x0) =
    (if glAllSecretArmTaint.gpr .x0 = .pub then (umulhArmState 0#64 0#64).gpr .x0
      else (umulhArmState 7#64 5#64).gpr .x0))
  rw [glAllSecretArmTaint_gpr_x0]
  decide

/-- `#tooth`: the contract needs checker-accepted entries. Over all `x86_64` programs and all
    states the leakage function has no contract: `div` leaks its operands with `DOITM` set. -/
theorem tooth_x86_unrestricted_programs_have_no_dit_contract :
    ¬ ∃ c : Spec.DitHardwareContract (List X86Stmt) X86State (List LeakageEvent),
      c.observe = fun mode prog s =>
        (execX86Prog prog 0 { s with doitEnabled := mode.ditEnabled,
                                     ymmUpperDirty := !mode.cleanSimdUpper }).2 := by
  rintro ⟨c, hObs⟩
  have h := c.dataIndependent [.instr (.div64 .rdi), .ret] (defaultX86State 3#64)
    (defaultX86State 17#64)
  rw [hObs] at h
  exact div64X86Prog_leaks _ _ h

end Qsag.ConstantTimeIsa

/-! ## §5. Compiled `.rlib` `ELF64` Symbol Contracts (`28` `qsag-asm` Kernels)

Connects `Spec.DitHardwareContract` directly to the decoded `x86_64` (`19` symbols, `1,935`
instructions) and `aarch64` (`9` symbols, `1,420` instructions) `.rlib` archives certified in
`Machine.ElfVerify` and `Machine.ElfFixtureVerify`, complementing §4's `ConstantTimeIsa`
microarchitectural `umulh`/`div` model with the production `qsag-asm` binary contracts. -/

namespace Qsag

attribute [-instance] UInt8.instLawfulEqOrd UInt64.instLawfulEqOrd BitVec.instLawfulEqOrd
  UInt64.instLawfulOrderOrd Std.instLawfulEqOrdOfLawfulOrderOrdOfAntisymmLe

private theorem bank16_get_ofFn {α : Type} (f : Nat → α) (r : Nat) (hr : r < 16) :
    (Bank16.ofFn f).get r = f r := by
  match r, hr with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _
  | 8, _ | 9, _ | 10, _ | 11, _ | 12, _ | 13, _ | 14, _ | 15, _ => rfl
  | k + 16, h => exact absurd h (Nat.not_lt_of_ge (Nat.le_add_left 16 k))

private theorem bank32_get_ofFn {α : Type} (f : Nat → α) (r : Nat) (hr : r < 32) :
    (Bank32.ofFn f).get r = f r := by
  match r, hr with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _
  | 8, _ | 9, _ | 10, _ | 11, _ | 12, _ | 13, _ | 14, _ | 15, _
  | 16, _ | 17, _ | 18, _ | 19, _ | 20, _ | 21, _ | 22, _ | 23, _
  | 24, _ | 25, _ | 26, _ | 27, _ | 28, _ | 29, _ | 30, _ | 31, _ => rfl
  | k + 32, h => exact absurd h (Nat.not_lt_of_ge (Nat.le_add_left 32 k))

/-- Decidable check whether byte address `a` lies in one of `c.pubMemRegions` under caller frame `pub`. -/
def inContractPubMem (c : FuncContract) (pub : Qsag.X86State) (a : UInt64) : Bool :=
  c.pubMemRegions.any (fun rl =>
    (List.range rl.2).any (fun off => a == pub.gpr.get rl.1 + UInt64.ofNat off))

private theorem inContractPubMem_hit {c : FuncContract} {pub : Qsag.X86State}
    {rl : Nat × Nat} (hRl : rl ∈ c.pubMemRegions) {off : Nat} (hOff : off < rl.2) :
    inContractPubMem c pub (pub.gpr.get rl.1 + UInt64.ofNat off) = true := by
  unfold inContractPubMem
  exact List.any_eq_true.mpr ⟨rl, hRl,
    List.any_eq_true.mpr ⟨off, List.mem_range.mpr hOff, beq_self_eq_true _⟩⟩

/-- Certified decoded `x86_64` `.text` slice entry paired with its `FuncContract` and public ABI frame. -/
structure ElfX86CtEntry where
  slice : ElfFuncSlice
  contract : FuncContract
  fuel : Nat
  pub : Qsag.X86State
  hMachine : slice.machine = elfMachineX86_64
  hPubLt : ∀ r ∈ contract.pubGprs, r < 16
  hMemPub : ∀ rl ∈ contract.pubMemRegions, rl.1 ∈ contract.pubGprs ∧ rl.1 < 16
  hFramePub : contract.usesRbpFrame = true →
    4 ∈ contract.pubGprs ∧ contract.outPtrReg ∈ contract.pubGprs ∧ contract.outPtrReg < 16
  hFrame : X86FramePrecond contract pub
  hSafe : ElfSliceThreeWayNISafe slice contract

/-- Merge public ABI pointers/lengths/LUT bytes from `e.pub` with secret GPRs/YMMs/flags/memory from `sec`,
    wiring `ymmDirty := !mode.cleanSimdUpper` from `Spec.ExecMode`. -/
def ElfX86CtEntry.entryState (e : ElfX86CtEntry) (mode : Spec.ExecMode)
    (sec : Qsag.X86State) : Qsag.X86State where
  pc := 0
  gpr := Bank16.ofFn (fun r =>
    if e.contract.pubGprs.any (· == r) then e.pub.gpr.get r else sec.gpr.get r)
  ymm := sec.ymm
  cf := sec.cf
  ofFlag := sec.ofFlag
  zf := sec.zf
  ymmDirty := !mode.cleanSimdUpper
  halted := false
  mem := fun a => if inContractPubMem e.contract e.pub a then e.pub.mem a else sec.mem a

theorem ElfX86CtEntry.entryState_pub_gpr (e : ElfX86CtEntry) (mode : Spec.ExecMode)
    (sec : Qsag.X86State) {r : Nat} (hr : r ∈ e.contract.pubGprs) :
    (e.entryState mode sec).gpr.get r = e.pub.gpr.get r := by
  have hLt : r < 16 := e.hPubLt r hr
  have hAny : e.contract.pubGprs.any (· == r) = true :=
    List.any_eq_true.mpr ⟨r, hr, beq_self_eq_true r⟩
  show (Bank16.ofFn _).get r = e.pub.gpr.get r
  rw [bank16_get_ofFn _ r hLt, hAny]
  rfl

theorem ElfX86CtEntry.entryState_contractInit (e : ElfX86CtEntry)
    (d₁ d₂ : Qsag.X86State) :
    X86ContractInit e.contract
      (e.entryState Spec.ExecMode.constantTimeSafe d₁)
      (e.entryState Spec.ExecMode.constantTimeSafe d₂) := by
  have hClean : (e.entryState Spec.ExecMode.constantTimeSafe d₁).ymmDirty = false := by
    change (!Spec.ExecMode.constantTimeSafe.cleanSimdUpper) = false
    rw [Spec.ExecMode.constantTimeSafe_flags.2.1]
    rfl
  have hClean2 : (e.entryState Spec.ExecMode.constantTimeSafe d₂).ymmDirty = false := hClean
  have hFrameOne : ∀ d : Qsag.X86State,
      X86FramePrecond e.contract (e.entryState Spec.ExecMode.constantTimeSafe d) := by
    intro d
    rw [X86FramePrecond.public_eq_1]
    cases hRbp : e.contract.usesRbpFrame with
    | false => exact Or.inl rfl
    | true =>
      obtain ⟨h4Mem, hOutMem, hOutLt⟩ := e.hFramePub hRbp
      have hPubFrame := e.hFrame
      rw [X86FramePrecond.public_eq_1] at hPubFrame
      rcases hPubFrame with hFalse | ⟨_, hRsp, hDisj⟩
      · rw [hRbp] at hFalse; cases hFalse
      · right
        rw [e.entryState_pub_gpr _ d h4Mem, e.entryState_pub_gpr _ d hOutMem]
        exact ⟨hOutLt, hRsp, hDisj⟩
  rw [X86ContractInit.public_eq_1]
  refine ⟨rfl, rfl, rfl, rfl, hClean, hClean2, ?_, ?_, hFrameOne d₁, hFrameOne d₂⟩
  · intro r hr
    exact ⟨e.hPubLt r hr,
      (e.entryState_pub_gpr _ d₁ hr).trans (e.entryState_pub_gpr _ d₂ hr).symm⟩
  · intro rl hRl
    obtain ⟨hRegMem, hRegLt⟩ := e.hMemPub rl hRl
    refine ⟨hRegLt, fun off hOff => ?_⟩
    rw [e.entryState_pub_gpr _ d₁ hRegMem, e.entryState_pub_gpr _ d₂ hRegMem]
    have hHit := inContractPubMem_hit (pub := e.pub) hRl hOff
    show (if inContractPubMem e.contract e.pub _ then _ else _) =
      (if inContractPubMem e.contract e.pub _ then _ else _)
    simp only [hHit, ↓reduceIte]

/-- Decoded `x86_64` `StepObs` leakage trace (`PC`, memory-access addresses, `isDoitSafe`). -/
def elfX86Leakage (mode : Spec.ExecMode) (e : ElfX86CtEntry) (sec : Qsag.X86State) :
    List StepObs :=
  match decodeX86Stream e.slice.code with
  | none => []
  | some prog => (runX86 prog e.fuel (e.entryState mode sec)).2

/-- `Spec.DitHardwareContract` instantiated directly over decoded `x86_64` `ELF64` `.text` slices. -/
def elfX86DitContract : Spec.DitHardwareContract ElfX86CtEntry Qsag.X86State (List StepObs) where
  observe := elfX86Leakage
  dataIndependent e d₁ d₂ := by
    have hSafe := e.hSafe
    rw [ElfSliceThreeWayNISafe.public_eq_1] at hSafe
    rcases hSafe with ⟨_, hX86⟩ | ⟨hArmMach, _⟩
    · obtain ⟨prog, hDec, hTraceEq, _, _⟩ :=
        hX86 _ _ (e.entryState_contractInit d₁ d₂) e.fuel
      simp only [elfX86Leakage, hDec]
      exact hTraceEq
    · exact absurd (e.hMachine.symm.trans hArmMach) (by decide)

/-- Certified decoded `aarch64` `.text` slice entry paired with its `FuncContract` and public ABI frame. -/
structure ElfArm64CtEntry where
  slice : ElfFuncSlice
  contract : FuncContract
  fuel : Nat
  pub : Arm64State
  hMachine : slice.machine = elfMachineAArch64
  hDoit : contract.doitEnabled = true
  hPubLt : ∀ r ∈ contract.pubGprs, r < 31
  hSafe : ElfSliceThreeWayNISafe slice contract

/-- Merge public ABI `x0..x30` pointers/counts from `e.pub` with secret GPRs/NEON/flags/memory from `sec`,
    wiring `PSTATE.DIT := mode.ditEnabled` from `Spec.ExecMode`. -/
def ElfArm64CtEntry.entryState (e : ElfArm64CtEntry) (mode : Spec.ExecMode)
    (sec : Arm64State) : Arm64State where
  pc := 0
  gpr := Bank32.ofFn (fun r =>
    if e.contract.pubGprs.any (· == r) then e.pub.gpr.get r else sec.gpr.get r)
  vec := sec.vec
  cf := sec.cf
  zf := sec.zf
  dit := mode.ditEnabled
  halted := false
  mem := sec.mem

theorem ElfArm64CtEntry.entryState_pub_gpr (e : ElfArm64CtEntry) (mode : Spec.ExecMode)
    (sec : Arm64State) {r : Nat} (hr : r ∈ e.contract.pubGprs) :
    (e.entryState mode sec).gpr.get r = e.pub.gpr.get r := by
  have hLt : r < 32 := Nat.lt_trans (e.hPubLt r hr) (by decide)
  have hAny : e.contract.pubGprs.any (· == r) = true :=
    List.any_eq_true.mpr ⟨r, hr, beq_self_eq_true r⟩
  show (Bank32.ofFn _).get r = e.pub.gpr.get r
  rw [bank32_get_ofFn _ r hLt, hAny]
  rfl

theorem ElfArm64CtEntry.entryState_contractInit (e : ElfArm64CtEntry)
    (d₁ d₂ : Arm64State) :
    Arm64ContractInit e.contract
      (e.entryState Spec.ExecMode.constantTimeSafe d₁)
      (e.entryState Spec.ExecMode.constantTimeSafe d₂) := by
  have hDit : (e.entryState Spec.ExecMode.constantTimeSafe d₁).dit = e.contract.doitEnabled := by
    show Spec.ExecMode.constantTimeSafe.ditEnabled = e.contract.doitEnabled
    rw [Spec.ExecMode.constantTimeSafe_flags.1, e.hDoit]
  rw [Arm64ContractInit.public_eq_1]
  refine ⟨rfl, rfl, rfl, rfl, hDit, hDit, fun r hr => ?_⟩
  exact ⟨e.hPubLt r hr,
    (e.entryState_pub_gpr _ d₁ hr).trans (e.entryState_pub_gpr _ d₂ hr).symm⟩

/-- Decoded `aarch64` `StepObs` leakage trace (`PC`, memory-access addresses, `isDoitSafe`). -/
def elfArm64Leakage (mode : Spec.ExecMode) (e : ElfArm64CtEntry) (sec : Arm64State) :
    List StepObs :=
  match decodeArm64Stream e.slice.code with
  | none => []
  | some prog => (runArm64 prog e.fuel (e.entryState mode sec)).2

/-- `Spec.DitHardwareContract` instantiated directly over decoded `aarch64` `ELF64` `.text` slices. -/
def elfArm64DitContract : Spec.DitHardwareContract ElfArm64CtEntry Arm64State (List StepObs) where
  observe := elfArm64Leakage
  dataIndependent e d₁ d₂ := by
    have hSafe := e.hSafe
    rw [ElfSliceThreeWayNISafe.public_eq_1] at hSafe
    rcases hSafe with ⟨hX86Mach, _⟩ | ⟨_, hArm⟩
    · exact absurd (e.hMachine.symm.trans hX86Mach) (by decide)
    · obtain ⟨prog, hDec, hTraceEq, _, _⟩ :=
        hArm _ _ (e.entryState_contractInit d₁ d₂) e.fuel
      simp only [elfArm64Leakage, hDec]
      exact hTraceEq

/-! ### Binding all `28` compiled `.rlib` symbols (`19` `x86_64` + `9` `aarch64`) -/

def x86ContractEntryWf (c : FuncContract) : Bool :=
  c.pubGprs.all (· < 16) &&
  c.pubMemRegions.all (fun rl => c.pubGprs.any (· == rl.1) && decide (rl.1 < 16)) &&
  (!c.usesRbpFrame ||
    (c.pubGprs.any (· == 4) && c.pubGprs.any (· == c.outPtrReg) &&
     decide (c.outPtrReg < 16) && decide (c.outPtrReg != 4) && decide (c.outBytes ≤ 0x10000)))

def arm64ContractEntryWf (c : FuncContract) : Bool :=
  c.doitEnabled && c.pubGprs.all (· < 31)

theorem currentX86SymbolContracts_all_wf :
    currentX86SymbolContracts.all x86ContractEntryWf = true := by decide

theorem currentAarch64SymbolContracts_all_wf :
    currentAarch64SymbolContracts.all arm64ContractEntryWf = true := by decide

theorem currentX86ExtractedSlices_all_x86_machine :
    currentX86ExtractedSlices.all (fun s => s.machine == elfMachineX86_64) = true := by
  decide +kernel

theorem currentAarch64ExtractedSlices_all_aarch64_machine :
    currentAarch64ExtractedSlices.all (fun s => s.machine == elfMachineAArch64) = true := by
  decide +kernel

/-- Canonical non-aliasing public ABI frame (`rsp = 0x80000`, public pointers at `0x10000`)
    valid for every contract in `currentX86SymbolContracts`. -/
def rlibX86DefaultPubState : Qsag.X86State where
  pc := 0
  gpr := Bank16.ofFn (fun r => if r == 4 then 0x80000 else 0x10000)
  ymm := Bank16.const Vec256.zero
  cf := false
  ofFlag := false
  zf := false
  ymmDirty := false
  halted := false
  mem := fun _ => 0x11

private theorem rlibX86DefaultPubState_frame {c : FuncContract}
    (hWf : x86ContractEntryWf c = true) :
    X86FramePrecond c rlibX86DefaultPubState := by
  unfold x86ContractEntryWf at hWf
  rcases Bool.and_eq_true_iff.mp hWf with ⟨_, hRbpPart⟩
  rw [X86FramePrecond.public_eq_1]
  cases hRbp : c.usesRbpFrame with
  | false => exact Or.inl rfl
  | true =>
    rw [hRbp] at hRbpPart
    simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne] at hRbpPart
    rcases hRbpPart with ⟨⟨⟨⟨_, _⟩, hOutLt⟩, hOutNe4⟩, hOutSz⟩
    right
    have hSp : rlibX86DefaultPubState.gpr.get 4 = (0x80000 : UInt64) := rfl
    have hOut : rlibX86DefaultPubState.gpr.get c.outPtrReg = (0x10000 : UInt64) := by
      show (Bank16.ofFn (fun r => if r == 4 then (0x80000 : UInt64) else 0x10000)).get c.outPtrReg = 0x10000
      rw [bank16_get_ofFn _ c.outPtrReg hOutLt]
      have hBeq : (c.outPtrReg == 4) = false := beq_false_of_ne hOutNe4
      rw [hBeq]
      rfl
    refine ⟨hOutLt, by rw [hSp]; decide, fun j k hj hk hEq => ?_⟩
    rw [hOut, hSp] at hEq
    have hNat := congrArg UInt64.toNat hEq
    have h64 : (2 : Nat) ^ 64 = 0x10000000000000000 := rfl
    have h10000 : (0x10000 : UInt64).toNat = 0x10000 := rfl
    have h7fff8 : ((0x80000 : UInt64) - 8).toNat = 0x7FFF8 := rfl
    simp only [UInt64.toNat_add, UInt64.toNat_ofNat', h10000, h7fff8, h64] at hNat
    omega

private theorem currentX86_idx_props (idx : Fin 19) :
    have hs : idx.val < currentX86ExtractedSlices.length := idx.isLt
    have hc : idx.val < currentX86SymbolContracts.length := idx.isLt
    (currentX86ExtractedSlices[idx.val]'hs).machine = elfMachineX86_64 ∧
    x86ContractEntryWf (currentX86SymbolContracts[idx.val]'hc) = true ∧
    ElfSliceThreeWayNISafe (currentX86ExtractedSlices[idx.val]'hs)
      (currentX86SymbolContracts[idx.val]'hc) := by
  have hs : idx.val < currentX86ExtractedSlices.length := idx.isLt
  have hc : idx.val < currentX86SymbolContracts.length := idx.isLt
  refine ⟨beq_iff_eq.mp (List.all_eq_true.mp currentX86ExtractedSlices_all_x86_machine _
      (List.getElem_mem hs)),
    List.all_eq_true.mp currentX86SymbolContracts_all_wf _ (List.getElem_mem hc),
    (certSliceAt_sound currentX86_all_symbol_certificates idx.val hs hc).2⟩

private theorem x86ContractEntryWf_pubLt {c : FuncContract}
    (hWf : x86ContractEntryWf c = true) : ∀ r ∈ c.pubGprs, r < 16 := by
  intro r hr
  have h1 := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hWf).1).1
  exact of_decide_eq_true (List.all_eq_true.mp h1 r hr)

private theorem x86ContractEntryWf_memPub {c : FuncContract}
    (hWf : x86ContractEntryWf c = true) :
    ∀ rl ∈ c.pubMemRegions, rl.1 ∈ c.pubGprs ∧ rl.1 < 16 := by
  intro rl hRl
  have h2 := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hWf).1).2
  have hRlOk := Bool.and_eq_true_iff.mp (List.all_eq_true.mp h2 rl hRl)
  obtain ⟨r', hr'Mem, hr'Eq⟩ := List.any_eq_true.mp hRlOk.1
  rw [beq_iff_eq.mp hr'Eq] at hr'Mem
  exact ⟨hr'Mem, of_decide_eq_true hRlOk.2⟩

private theorem x86ContractEntryWf_framePub {c : FuncContract}
    (hWf : x86ContractEntryWf c = true) (hRbp : c.usesRbpFrame = true) :
    4 ∈ c.pubGprs ∧ c.outPtrReg ∈ c.pubGprs ∧ c.outPtrReg < 16 := by
  unfold x86ContractEntryWf at hWf
  have h3 := (Bool.and_eq_true_iff.mp hWf).2
  rw [hRbp] at h3
  simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at h3
  rcases h3 with ⟨⟨⟨⟨h4Any, hOutAny⟩, hOutLt⟩, _⟩, _⟩
  obtain ⟨r4, hr4Mem, hr4Eq⟩ := List.any_eq_true.mp h4Any
  obtain ⟨ro, hroMem, hroEq⟩ := List.any_eq_true.mp hOutAny
  rw [beq_iff_eq.mp hr4Eq] at hr4Mem
  rw [beq_iff_eq.mp hroEq] at hroMem
  exact ⟨hr4Mem, hroMem, hOutLt⟩

/-- Construct the certified `ElfX86CtEntry` for any of the `19` compiled `qsag-asm` `x86_64` `.rlib` symbols. -/
def rlibX86CtEntry (idx : Fin 19) (fuel : Nat) : ElfX86CtEntry :=
  let hs : idx.val < currentX86ExtractedSlices.length := idx.isLt
  let hc : idx.val < currentX86SymbolContracts.length := idx.isLt
  let hProps := currentX86_idx_props idx
  { slice := currentX86ExtractedSlices[idx.val]'hs
    contract := currentX86SymbolContracts[idx.val]'hc
    fuel := fuel
    pub := rlibX86DefaultPubState
    hMachine := hProps.1
    hPubLt := x86ContractEntryWf_pubLt hProps.2.1
    hMemPub := x86ContractEntryWf_memPub hProps.2.1
    hFramePub := x86ContractEntryWf_framePub hProps.2.1
    hFrame := rlibX86DefaultPubState_frame hProps.2.1
    hSafe := hProps.2.2 }

theorem rlibX86CtEntry_binds_rlib_archive (idx : Fin 19) (fuel : Nat) :
    (extractAllRlibFuncs currentX86RlibArchiveBytes)[idx.val]? =
      some (rlibX86CtEntry idx fuel).slice ∧
    currentX86SymbolContracts[idx.val]? =
      some (rlibX86CtEntry idx fuel).contract := by
  rw [currentX86_rlib_extracted_slices]
  exact ⟨List.getElem?_eq_getElem idx.isLt, List.getElem?_eq_getElem idx.isLt⟩

private theorem currentAarch64_idx_props (idx : Fin 9) :
    have hs : idx.val < currentAarch64ExtractedSlices.length := idx.isLt
    have hc : idx.val < currentAarch64SymbolContracts.length := idx.isLt
    (currentAarch64ExtractedSlices[idx.val]'hs).machine = elfMachineAArch64 ∧
    arm64ContractEntryWf (currentAarch64SymbolContracts[idx.val]'hc) = true ∧
    ElfSliceThreeWayNISafe (currentAarch64ExtractedSlices[idx.val]'hs)
      (currentAarch64SymbolContracts[idx.val]'hc) := by
  have hs : idx.val < currentAarch64ExtractedSlices.length := idx.isLt
  have hc : idx.val < currentAarch64SymbolContracts.length := idx.isLt
  refine ⟨beq_iff_eq.mp (List.all_eq_true.mp currentAarch64ExtractedSlices_all_aarch64_machine _
      (List.getElem_mem hs)),
    List.all_eq_true.mp currentAarch64SymbolContracts_all_wf _ (List.getElem_mem hc),
    (certSliceAt_sound currentAarch64_all_symbol_certificates idx.val hs hc).2⟩

/-- Construct the certified `ElfArm64CtEntry` for any of the `9` compiled `qsag-asm` `aarch64` `.rlib` symbols. -/
def rlibArm64CtEntry (idx : Fin 9) (fuel : Nat) (pub : Arm64State) : ElfArm64CtEntry :=
  let hs : idx.val < currentAarch64ExtractedSlices.length := idx.isLt
  let hc : idx.val < currentAarch64SymbolContracts.length := idx.isLt
  let hProps := currentAarch64_idx_props idx
  { slice := currentAarch64ExtractedSlices[idx.val]'hs
    contract := currentAarch64SymbolContracts[idx.val]'hc
    fuel := fuel
    pub := pub
    hMachine := hProps.1
    hDoit := (Bool.and_eq_true_iff.mp hProps.2.1).1
    hPubLt := fun r hr =>
      of_decide_eq_true (List.all_eq_true.mp (Bool.and_eq_true_iff.mp hProps.2.1).2 r hr)
    hSafe := hProps.2.2 }

theorem rlibArm64CtEntry_binds_rlib_archive (idx : Fin 9) (fuel : Nat) (pub : Arm64State) :
    (extractAllRlibFuncs currentAarch64RlibArchiveBytes)[idx.val]? =
      some (rlibArm64CtEntry idx fuel pub).slice ∧
    currentAarch64SymbolContracts[idx.val]? =
      some (rlibArm64CtEntry idx fuel pub).contract := by
  rw [currentAarch64_rlib_extracted_slices]
  exact ⟨List.getElem?_eq_getElem idx.isLt, List.getElem?_eq_getElem idx.isLt⟩

/-- Every multi-call invocation trace of the `19` compiled `x86_64` `.rlib` kernels with matching
    `(symbolIdx, fuel)` schedule produces identical `StepObs` leakage traces under `constantTimeSafe`,
    regardless of secret GPRs, YMM registers, flags, and secret memory. -/
theorem rlib_x86_all19_dit_trace_data_independent
    (tr₁ tr₂ : List ((Fin 19 × Nat) × Qsag.X86State))
    (hSched : tr₁.map Prod.fst = tr₂.map Prod.fst) :
    tr₁.map (fun call => elfX86Leakage Spec.ExecMode.constantTimeSafe
        (rlibX86CtEntry call.1.1 call.1.2) call.2) =
      tr₂.map (fun call => elfX86Leakage Spec.ExecMode.constantTimeSafe
        (rlibX86CtEntry call.1.1 call.1.2) call.2) := by
  let liftCall := fun (call : (Fin 19 × Nat) × Qsag.X86State) =>
    (rlibX86CtEntry call.1.1 call.1.2, call.2)
  have hMapEq : (tr₁.map liftCall).map Prod.fst = (tr₂.map liftCall).map Prod.fst := by
    have h1 := congrArg (List.map (fun p : Fin 19 × Nat => rlibX86CtEntry p.1 p.2)) hSched
    simpa only [List.map_map, Function.comp_def, liftCall] using h1
  have hRes := elfX86DitContract.trace_data_independent Spec.ExecMode.constantTimeSafe rfl
    (tr₁.map liftCall) (tr₂.map liftCall) hMapEq
  simpa only [List.map_map, Function.comp_def, elfX86DitContract] using hRes

/-- Every multi-call invocation trace of the `9` compiled `aarch64` `.rlib` kernels with matching
    `(symbolIdx, fuel, pub)` schedule produces identical `StepObs` leakage traces under `constantTimeSafe`,
    regardless of secret GPRs, NEON vectors, flags, and secret memory. -/
theorem rlib_aarch64_all9_dit_trace_data_independent
    (tr₁ tr₂ : List ((Fin 9 × Nat × Arm64State) × Arm64State))
    (hSched : tr₁.map Prod.fst = tr₂.map Prod.fst) :
    tr₁.map (fun call => elfArm64Leakage Spec.ExecMode.constantTimeSafe
        (rlibArm64CtEntry call.1.1 call.1.2.1 call.1.2.2) call.2) =
      tr₂.map (fun call => elfArm64Leakage Spec.ExecMode.constantTimeSafe
        (rlibArm64CtEntry call.1.1 call.1.2.1 call.1.2.2) call.2) := by
  let liftCall := fun (call : (Fin 9 × Nat × Arm64State) × Arm64State) =>
    (rlibArm64CtEntry call.1.1 call.1.2.1 call.1.2.2, call.2)
  have hMapEq : (tr₁.map liftCall).map Prod.fst = (tr₂.map liftCall).map Prod.fst := by
    have h1 := congrArg (List.map (fun p : Fin 9 × Nat × Arm64State =>
      rlibArm64CtEntry p.1 p.2.1 p.2.2)) hSched
    simpa only [List.map_map, Function.comp_def, liftCall] using h1
  have hRes := elfArm64DitContract.trace_data_independent Spec.ExecMode.constantTimeSafe rfl
    (tr₁.map liftCall) (tr₂.map liftCall) hMapEq
  simpa only [List.map_map, Function.comp_def, elfArm64DitContract] using hRes

/-- Inhabitedness witness exercising real `.rlib` symbol `8` (`qsag_asm_goldilocks_mul_ct_x86_64`)
    on distinct secret operands (`rdi = 3 ≠ 7`) with identical `StepObs` leakage trace. -/
theorem inhabited_rlib_x86_dit_sequence :
    ∃ tr₁ tr₂ : List ((Fin 19 × Nat) × Qsag.X86State),
      tr₁.map Prod.fst = tr₂.map Prod.fst ∧
      ¬ (tr₁.map (fun c => c.2.gpr.get 7) = tr₂.map (fun c => c.2.gpr.get 7)) ∧
      tr₁.map (fun call => elfX86Leakage Spec.ExecMode.constantTimeSafe
          (rlibX86CtEntry call.1.1 call.1.2) call.2) =
        tr₂.map (fun call => elfX86Leakage Spec.ExecMode.constantTimeSafe
          (rlibX86CtEntry call.1.1 call.1.2) call.2) := by
  let s1 : Qsag.X86State := { rlibX86DefaultPubState with
    gpr := Bank16.ofFn (fun r => if r == 7 then 3 else 0x10000) }
  let s2 : Qsag.X86State := { rlibX86DefaultPubState with
    gpr := Bank16.ofFn (fun r => if r == 7 then 7 else 0x10000) }
  refine ⟨[((⟨8, by decide⟩, 64), s1)], [((⟨8, by decide⟩, 64), s2)], rfl, by decide, ?_⟩
  exact rlib_x86_all19_dit_trace_data_independent _ _ rfl

/-- `#tooth`: patching the compiled `qsag_asm_gf256_shamir_mul_gfni` `.rlib` slice (`rlibX86CtEntry 2`)
    to NOP its vector-clear epilogue violates the 3-way constant-time + SIMD-hygiene contract. -/
theorem tooth_rlib_x86_gfni_missing_vzeroupper_rejected :
    checkX86WithInv (patchBytesAt (rlibX86CtEntry ⟨2, by decide⟩ 0).slice.code 0x72
      [0x90, 0x90, 0x90, 0x90, 0x90])
      (rlibX86CtEntry ⟨2, by decide⟩ 0).contract qsag_asm_gf256_shamir_mul_gfni_currentInv = false :=
  current_gfni_missing_vector_cleanup_rejected

/-- `#tooth`: patching the compiled `qsag_asm_tower128_bdoz_mac_pmull` `.rlib` slice (`rlibArm64CtEntry 3`)
    to NOP its NEON zeroization epilogue violates the `aarch64` constant-time contract. -/
theorem tooth_rlib_aarch64_pmull_missing_neon_wipe_rejected (pub : Arm64State) :
    checkArm64WithInv (patchBytesAt (rlibArm64CtEntry ⟨3, by decide⟩ 0 pub).slice.code 0x104
      [0x1F, 0x20, 0x03, 0xD5])
      (rlibArm64CtEntry ⟨3, by decide⟩ 0 pub).contract
      qsag_asm_tower128_bdoz_mac_pmull_currentInv = false :=
  current_pmull_missing_wipe_rejected

/-- A concrete symbol-index witness for the rejected GFNI epilogue mutation. -/
theorem tooth_rlib_x86_gfni_mutation_witness :
    ∃ idx : Fin 19, idx = ⟨2, by decide⟩ ∧
      checkX86WithInv (patchBytesAt (rlibX86CtEntry idx 0).slice.code 0x72
        [0x90, 0x90, 0x90, 0x90, 0x90])
        (rlibX86CtEntry idx 0).contract qsag_asm_gf256_shamir_mul_gfni_currentInv = false :=
  ⟨⟨2, by decide⟩, rfl, tooth_rlib_x86_gfni_missing_vzeroupper_rejected⟩

/-- A concrete symbol-index witness for the rejected PMULL epilogue mutation. -/
theorem tooth_rlib_aarch64_pmull_mutation_witness (pub : Arm64State) :
    ∃ idx : Fin 9, idx = ⟨3, by decide⟩ ∧
      checkArm64WithInv (patchBytesAt (rlibArm64CtEntry idx 0 pub).slice.code 0x104
        [0x1F, 0x20, 0x03, 0xD5])
        (rlibArm64CtEntry idx 0 pub).contract
        qsag_asm_tower128_bdoz_mac_pmull_currentInv = false :=
  ⟨⟨3, by decide⟩, rfl, tooth_rlib_aarch64_pmull_missing_neon_wipe_rejected pub⟩

end Qsag
end

#verify_constructive Qsag.simtEpochContract_uniformControlFlow
#verify_constructive Qsag.simtEpochContract_memory_independent
#verify_constructive Qsag.simtEpochContract_wellFormed_of_ownerCheck
#verify_constructive Qsag.twoWaveReduction_epochs_wellFormed
#verify_constructive Qsag.twoWaveReduction_write_race_free
#verify_constructive Qsag.twoWavePhase0_contract_memory_independent
#verify_constructive Qsag.twoWaveNoBarrier_not_wellFormed
#verify_constructive Qsag.twoWavePhase1_accepted_by_simtCt
#verify_constructive Qsag.twoWavePhase1_contract_memory_independent
#verify_constructive Qsag.twoWave_mistyped_output_rejected_by_simtCt
#verify_constructive Qsag.twoWaveNoBarrier_schedule_dependent
#verify_constructive Qsag.faial_disjointStorageBindings
#verify_constructive Qsag.nttStageAddressModel_disjointStorageBindings
#verify_constructive Qsag.ConstantTimeIsa.ArmCtEntry.entryState_lowEq
#verify_constructive Qsag.ConstantTimeIsa.X86CtEntry.entryState_lowEq
#verify_constructive Qsag.ConstantTimeIsa.arm_kernel_sequence_leakage_data_independent
#verify_constructive Qsag.ConstantTimeIsa.x86_kernel_sequence_leakage_data_independent
#verify_constructive Qsag.ConstantTimeIsa.tooth_arm_umulh_leaks_without_dit_mode
#verify_constructive Qsag.ConstantTimeIsa.tooth_x86_unrestricted_programs_have_no_dit_contract
#verify_constructive Qsag.ElfX86CtEntry.entryState_contractInit
#verify_constructive Qsag.ElfArm64CtEntry.entryState_contractInit
#verify_constructive Qsag.rlibX86CtEntry_binds_rlib_archive
#verify_constructive Qsag.rlibArm64CtEntry_binds_rlib_archive
#verify_constructive Qsag.rlib_x86_all19_dit_trace_data_independent
#verify_constructive Qsag.rlib_aarch64_all9_dit_trace_data_independent
#verify_constructive Qsag.inhabited_rlib_x86_dit_sequence
#verify_constructive Qsag.tooth_rlib_x86_gfni_missing_vzeroupper_rejected
#verify_constructive Qsag.tooth_rlib_aarch64_pmull_missing_neon_wipe_rejected
#tooth_pair Qsag.twoWaveReduction_epochs_wellFormed vs Qsag.twoWaveNoBarrier_not_wellFormed
#tooth_pair Qsag.ConstantTimeIsa.arm_kernel_sequence_leakage_data_independent vs Qsag.ConstantTimeIsa.tooth_arm_umulh_leaks_without_dit_mode
set_option maxRecDepth 65536 in
#tooth_pair Qsag.rlib_x86_all19_dit_trace_data_independent vs Qsag.tooth_rlib_x86_gfni_mutation_witness
set_option maxRecDepth 65536 in
#tooth_pair Qsag.rlib_aarch64_all9_dit_trace_data_independent vs Qsag.tooth_rlib_aarch64_pmull_mutation_witness
#verify_inhabited Qsag.ConstantTimeIsa.arm_kernel_sequence_leakage_data_independent Qsag.ConstantTimeIsa.inhabited_arm_kernel_sequence
#verify_inhabited Qsag.rlib_x86_all19_dit_trace_data_independent Qsag.inhabited_rlib_x86_dit_sequence
