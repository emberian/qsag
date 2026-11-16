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
* §3 `nttStageAddressModel`: an address-formula model of one fused stage of
  `goldilocks_ntt.comp` (256 invocations, 8 Wave32 subgroups). It is not an instance built from
  a kernel: the Machine layer has no instruction stream for that shader, so the block traces
  are empty and the access sets are written by hand from the formulas `productionButterflyIndex`
  and `productionLdsIndex`. The one fact proved is that these formulas give disjoint cells.
* §4 `armDitContract`, `x86DitContract`: `observe` is the leakage trace of `execArmProg` /
  `execX86Prog` on a checker-accepted kernel entry; the data are the secret-labelled registers,
  flags and memory. The `ExecMode` enters through the initial `ditEnabled` / `doitEnabled` /
  `ymmUpperDirty` bits of the machine state.
-/
public import Qsag.Spec.Assumptions
public import Qsag.Machine.SpirvSimt
public import Qsag.Machine.ConstantTimeIsa
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
    fun o ho => simt_ct_zero_exec_divergence env prog fuel _ mem rfl o ho
  have hLane : ∀ k : Nat, k % wave32Lanes < 32 := fun k => Nat.mod_lt k (by decide)
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
    fun w => simt_ct_noninterference hCt fuel (initWave_lowEq env pol cfg hScalar w) hMem
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
      exact h32
    have hl : i % wave32Lanes < wave32Lanes := Nat.mod_lt i (by decide)
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

theorem twoWavePhase0_ownerCheck (mem : GpuMemState) :
    simtEpochOwnerCheck twoWaveReductionEnv twoWaveCfg twoWavePhase0WriteLds 4 mem twoWaveLdsCell
      simtCellIndex = true := by
  kernel_rfl

theorem twoWavePhase1_ownerCheck (mem : GpuMemState) :
    simtEpochOwnerCheck twoWaveReductionEnv twoWaveCfg twoWavePhase1CrossWaveRead 8 mem
      twoWaveOutCell simtCellIndex = true := by
  kernel_rfl

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
      hi hj (List.mem_map_of_mem hci) (List.mem_map_of_mem hcj),
   fun hci hcj => (twoWaveReduction_epochs_wellFormed mem).2.write_race_free i j (simtCellCode c)
      hi hj (List.mem_map_of_mem hci) (List.mem_map_of_mem hcj)⟩

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
  have hScalar : ScalarConstEnv twoWaveReductionEnv := by
    intro id sc b off w h
    simp only [twoWaveReductionEnv] at h
    split at h <;> cases h
  exact simtEpochContract_memory_independent (pol := twoWaveSecretDataPolicy) hScalar (by decide)
    twoWaveCfg 4 ⟨hPush, (fun h => SecLabel.noConfusion h), (fun _ h => SecLabel.noConfusion h)⟩

/-- The second reduction epoch is rejected by the `SIMT-CT` checker under every policy: its
    access chain `%19 = &outBuf[tid]` is typed with pointer type `%7`, which
    `twoWaveReductionEnv.ptrInfo` binds to storage buffer `0` while `%4` and `%19` are bound to
    storage buffer `1`. `simt_ct_noninterference` therefore does not apply to it. -/
theorem twoWavePhase1_rejected_by_simtCt (pol : SimtCtPolicy) :
    checkProgSimtCt twoWaveReductionEnv pol twoWavePhase1CrossWaveRead = false := by
  have h : checkInstSimtCtStrict twoWaveReductionEnv pol (.opAccessChain 7 19 4 [1]) = false := by
    simp [checkInstSimtCtStrict, twoWaveReductionEnv]
  unfold checkProgSimtCt twoWavePhase1CrossWaveRead
  simp only [List.all_cons, h, Bool.and_false, Bool.false_and]

theorem twoWaveNoBarrier_cross_wave_cell (mem : GpuMemState) :
    List.elem 16777220
        ((simtEpochContract twoWaveReductionEnv twoWaveCfg twoWaveNoBarrierEpoch 12 mem).writeSet
          32) = true ∧
      List.elem 16777220
        ((simtEpochContract twoWaveReductionEnv twoWaveCfg twoWaveNoBarrierEpoch 12 mem).readSet
          0) = true := by
  constructor <;> kernel_rfl

/-- **The barrier-free concatenation of the two reduction epochs is not well formed**, on any
    memory: invocation `32` stores `lds[32]` and invocation `0` loads it in the same epoch. The
    barrier between the two epochs is what makes each of them race free. -/
theorem twoWaveNoBarrier_not_wellFormed (mem : GpuMemState) :
    ¬ Spec.WellFormedSimtContract
      (simtEpochContract twoWaveReductionEnv twoWaveCfg twoWaveNoBarrierEpoch 12 mem) := by
  intro w
  have hi : 32 < (simtEpochContract twoWaveReductionEnv twoWaveCfg twoWaveNoBarrierEpoch 12
      mem).workgroupSize := (by decide : 32 < 64)
  have hj : 0 < (simtEpochContract twoWaveReductionEnv twoWaveCfg twoWaveNoBarrierEpoch 12
      mem).workgroupSize := (by decide : 0 < 64)
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
  ⟨{ lds := fun _ => 0
     ssbo := fun b idx => if b == 0 then (if idx < 32 then 10 else 42) else 0
     pushConsts := fun _ => 0 },
   List.replicate 12 0 ++ List.replicate 12 1,
   List.replicate 4 0 ++ List.replicate 4 1 ++ List.replicate 8 0 ++ List.replicate 8 1,
   by decide⟩

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

/-! ## §3. Address-formula model of one fused NTT stage of `goldilocks_ntt.comp` -/

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

/-- **Address-formula model** of one fused NTT stage; not a contract derived from the shader.
    The Machine layer has no instruction stream for `goldilocks_ntt.comp`, so nothing here is
    read off an execution: the block traces are empty (uniform control flow holds trivially and
    says nothing about the shader), and the access sets are the hand-written address formulas.
    The read set is set equal to the write set on the assumption that the butterfly is in
    place and the twiddle factors come from a read-only table outside the LDS; that the shader
    accesses exactly these cells is not proved. -/
def nttStageAddressModel (stage : Nat) : Spec.SimtWorkgroupContract where
  subgroupSize := wave32Lanes
  workgroupSize := productionNttCfg.totalThreads
  blockTrace _ := []
  writeSet := productionNttStageWrites stage
  readSet := productionNttStageWrites stage
  h_divides := ⟨by rw [wave32Lanes_eq]; decide,
    ⟨productionNttCfg.numWaves, by rw [productionNttCfg.totalThreads_eq, Nat.mul_comm]⟩⟩

set_option maxRecDepth 8192 in
private theorem productionNttWriter_checked :
    ∀ stage : Fin 9, ∀ lid : Fin 256,
      (productionNttStageWrites stage lid).all
        (fun cell => productionNttWriter stage cell == lid.val) = true := by
  decide +kernel

/-- In each of the nine fused stages the address formulas assign no LDS cell to two of the
    `256` invocations. This is a fact about the formulas of `nttStageAddressModel`, not about
    an execution of the shader. -/
theorem nttStageAddressModel_disjointStorageBindings (stage : Fin 9) :
    (nttStageAddressModel stage).DisjointStorageBindings := by
  intro i j hi hj hne cell hci
  have hi' : i < 256 := hi
  have hj' : j < 256 := hj
  have h1 := Nat.eq_of_beq_eq_true
    (List.all_eq_true.mp (productionNttWriter_checked stage ⟨i, hi'⟩) cell hci)
  have hNot : cell ∉ productionNttStageWrites stage j := fun hcj =>
    hne (h1.symm.trans (Nat.eq_of_beq_eq_true
      (List.all_eq_true.mp (productionNttWriter_checked stage ⟨j, hj'⟩) cell hcj)))
  exact ⟨hNot, hNot⟩

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

/-! ### Kernel entries of `qsag-asm` -/

def goldilocksMulArmEntry (pub : ArmState) : ArmCtEntry :=
  { prog := goldilocksMulCtArmProg, τ := glAllSecretArmTaint, memPol := fun _ => .sec,
    secHeap := true, hPol := fun _ _ => rfl, hCheck := rfl, pub := pub }

def ctEq32ArmEntry (pub : ArmState) : ArmCtEntry :=
  { prog := ctEq32ArmProg, τ := aapcsPtrArgs3Taint, memPol := fun _ => .sec,
    secHeap := true, hPol := fun _ _ => rfl, hCheck := rfl, pub := pub }

def keccakSha3NeonEntry (pub : ArmState) : ArmCtEntry :=
  { prog := keccakSha3NeonProg, τ := aapcsPtrArgs3Taint, memPol := fun _ => .sec,
    secHeap := true, hPol := fun _ _ => rfl, hCheck := rfl, pub := pub }

def goldilocksMulX86Entry (pub : X86State) : X86CtEntry :=
  { prog := goldilocksMulCtX86Prog, τ := glAllSecretX86Taint, memPol := fun _ => .sec,
    secHeap := true, hPol := fun _ _ => rfl, hCheck := rfl, pub := pub }

def ctEq32X86Entry (pub : X86State) : X86CtEntry :=
  { prog := ctEq32X86Prog, τ := sysvPtrArgs4Taint, memPol := fun _ => .sec,
    secHeap := true, hPol := fun _ _ => rfl, hCheck := rfl, pub := pub }

def keccakChiMpcAvx2Entry (pub : X86State) : X86CtEntry :=
  { prog := keccakChiMpcAvx2Prog, τ := sysvPtrArgs4Taint, memPol := fun _ => .sec,
    secHeap := true, hPol := fun _ _ => rfl, hCheck := rfl, pub := pub }

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
  ⟨[(goldilocksMulArmEntry (initGlArmState 0#64 0#64), initGlArmState 3#64 5#64)],
   [(goldilocksMulArmEntry (initGlArmState 0#64 0#64), initGlArmState 7#64 5#64)], rfl, by decide,
   arm_kernel_sequence_leakage_data_independent _ _ rfl⟩

/-- `#tooth`: the mode bit is needed. With `ditEnabled = false` the Goldilocks `aarch64` kernel
    leaks its `UMULH` operands. -/
theorem tooth_arm_goldilocks_leaks_without_dit_mode :
    ¬ (armLeakage { Spec.ExecMode.constantTimeSafe with ditEnabled := false }
          (goldilocksMulArmEntry (initGlArmState 0#64 0#64)) (initGlArmState 3#64 5#64) =
       armLeakage { Spec.ExecMode.constantTimeSafe with ditEnabled := false }
          (goldilocksMulArmEntry (initGlArmState 0#64 0#64)) (initGlArmState 7#64 5#64)) := by
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
  exact absurd h (by decide)

end Qsag.ConstantTimeIsa
end

#verify_constructive Qsag.simtEpochContract_uniformControlFlow
#verify_constructive Qsag.simtEpochContract_memory_independent
#verify_constructive Qsag.simtEpochContract_wellFormed_of_ownerCheck
#verify_constructive Qsag.twoWaveReduction_epochs_wellFormed
#verify_constructive Qsag.twoWaveReduction_write_race_free
#verify_constructive Qsag.twoWavePhase0_contract_memory_independent
#verify_constructive Qsag.twoWaveNoBarrier_not_wellFormed
#verify_constructive Qsag.twoWavePhase1_rejected_by_simtCt
#verify_constructive Qsag.twoWaveNoBarrier_schedule_dependent
#verify_constructive Qsag.faial_disjointStorageBindings
#verify_constructive Qsag.nttStageAddressModel_disjointStorageBindings
#verify_constructive Qsag.ConstantTimeIsa.ArmCtEntry.entryState_lowEq
#verify_constructive Qsag.ConstantTimeIsa.X86CtEntry.entryState_lowEq
#verify_constructive Qsag.ConstantTimeIsa.arm_kernel_sequence_leakage_data_independent
#verify_constructive Qsag.ConstantTimeIsa.x86_kernel_sequence_leakage_data_independent
#verify_constructive Qsag.ConstantTimeIsa.tooth_arm_goldilocks_leaks_without_dit_mode
#verify_constructive Qsag.ConstantTimeIsa.tooth_x86_unrestricted_programs_have_no_dit_contract
#tooth_pair Qsag.twoWaveReduction_epochs_wellFormed vs Qsag.twoWaveNoBarrier_not_wellFormed
#tooth_pair Qsag.ConstantTimeIsa.arm_kernel_sequence_leakage_data_independent vs Qsag.ConstantTimeIsa.tooth_arm_goldilocks_leaks_without_dit_mode
#verify_inhabited Qsag.ConstantTimeIsa.arm_kernel_sequence_leakage_data_independent Qsag.ConstantTimeIsa.inhabited_arm_kernel_sequence
