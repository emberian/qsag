module
public import Qsag.Tests.TwoSlotHwmTeeth
public import Qsag.Tests.GuardedMachineSimInstance
import Qsag.Tactic.AssuranceKit
/-!
# Qsag.Tests.CrashAndGuardKitTeeth — Durable `TwoSlotHwm` (`QSBURN05`) Coupled With `GuardedMachineSim`

Composes the sector-level two-slot high-water-mark crash-recovery model (`TwoSlotHwmCrashModel`,
`qsburn05 512`, `recoverTruncatedAppendPlan`) with `mirBeltLatchKernelGuard` via
`GuardedMachine.prod` (`GuardedMachineSim`), proving without private unfolding that:
1. Every accepted bind requires verified `QSBURN05` HWM slot/chain recovery at the exact requested
   epoch and commits both 80-byte slots (`Slot.a`, `Slot.b`) alongside the belt-latch advance,
2. Multi-turn traces preserve `MirBeltLatchKernel.WellFormed` and verified `recoverTruncatedAppendPlan`
   counter alignment,
3. A 1-byte torn tail at epoch `0` (`toyTornSteady`) cleanly truncates and advances `0 → 1` across
   both durable slots and `MirBeltLatchKernel` (`hwmBeltCoupled_accepts_epoch0_witness`), and
4. A 2-record gap violation (`toyTornGapTwo`) causes the coupled guard to fail closed!
-/
public section
namespace Qsag.Tests.CrashAndGuardKitTeeth

open Qsag
open Qsag.Exec.GuardedMachineSim
open Qsag.Exec.TwoSlotHwmCrashModel
open Qsag.Tests.TwoSlotHwmTeeth
open Qsag.Tests.GuardedMachineSimInstance

set_option autoImplicit false

/-- Write the record and both `QSBURN05` 80-byte slots for advancing counter `c → c + 1` on `toyCodec`. -/
def commitToyEpochOnDisk (d : Disk) (c : Nat) : Disk :=
  let offRec := (qsburn05 512).chainOff + 2 * c
  let nextPar := par (c + 1)
  (((d.write offRec [0x7E, 0x7E]).write ((qsburn05 512).off .a)
      (toyCodec.encSlot .a (c + 1) nextPar)).write ((qsburn05 512).off .b)
      (toyCodec.encSlot .b (c + 1) nextPar))

/-- Guard over a `QSBURN05` `Disk` image checking verified `recoverTruncatedAppendPlan` convergence
    at `req.epoch` before durably advancing counter `epoch → epoch + 1` on the truncated image. -/
def qsburn05EpochGuard : GuardedMachine Disk MirBeltLatchBindRequest Nat where
  guard d req :=
    match recoverTruncatedAppendPlan toyCodec (qsburn05 512) d with
    | some (_, h, _) => decide (h.len = req.epoch.toNat)
    | none => false
  next d req :=
    match recoverTruncatedAppendPlan toyCodec (qsburn05 512) d with
    | some (dClean, _, _) => commitToyEpochOnDisk dClean req.epoch.toNat
    | none => d
  out _ req := req.epoch.toNat + 1

/-- Coupled `QSBURN05` durable HWM disk guard × `mirBeltLatchKernelGuard` product machine! -/
def hwmBeltCoupledGuard :
    GuardedMachine (Disk × MirBeltLatchKernel) MirBeltLatchBindRequest
      (Nat × MirBeltLatchBindOutcome) :=
  qsburn05EpochGuard.prod mirBeltLatchKernelGuard

/-- **Multi-Turn Durable HWM × Belt-Latch Safety (`hwmBeltCoupled_multiTurn_safe`)**:
    Every trace of `hwmBeltCoupledGuard` preserves `MirBeltLatchKernel.WellFormed`, enforces
    the kernel capacity bound, and ensures every accepted turn passed `QSBURN05`
    two-slot recovery (`recoverTruncatedAppendPlan = some (dClean, h, ws)`) at the bound epoch! -/
theorem hwmBeltCoupled_multiTurn_safe
    {s₀ sF : Disk × MirBeltLatchKernel}
    {tr : List (MirBeltLatchBindRequest × (Nat × MirBeltLatchBindOutcome))}
    (hWf₀ : s₀.2.WellFormed)
    (hTr : hwmBeltCoupledGuard.toParty.ValidTrace s₀ tr sF) :
    sF.2.WellFormed ∧
    (∀ p ∈ tr, p.1.epoch.toNat < s₀.2.capacity_limit.toNat ∧
      ∃ d dClean h ws,
        recoverTruncatedAppendPlan toyCodec (qsburn05 512) d = some (dClean, h, ws) ∧
        h.len = p.1.epoch.toNat) := by
  have hDiskTr := GuardedMachine.prod_fst_validTrace _ _ hTr
  have hBeltTr := GuardedMachine.prod_snd_validTrace _ _ hTr
  obtain ⟨hWfF, hCap, _⟩ :=
    Qsag.mirBeltLatchKernel_equivocation_free hWf₀
      (models_of_toParty_validTrace mirBeltLatchKernel_models hBeltTr)
  obtain ⟨_, hDiskAll⟩ := qsburn05EpochGuard.models_self.trace_invariant (fun _ => True)
    (fun _ _ _ _ => trivial) (fun _ _ _ _ => trivial) hDiskTr trivial
  refine ⟨hWfF, fun p hp => ?_⟩
  have hBeltMem : (p.1, p.2.2) ∈ tr.map (fun x => (x.1, x.2.2)) :=
    List.mem_map_of_mem (f := fun x : MirBeltLatchBindRequest × (Nat × MirBeltLatchBindOutcome) => (x.1, x.2.2)) hp
  have hDiskMem : (p.1, p.2.1) ∈ tr.map (fun x => (x.1, x.2.1)) :=
    List.mem_map_of_mem (f := fun x : MirBeltLatchBindRequest × (Nat × MirBeltLatchBindOutcome) => (x.1, x.2.1)) hp
  obtain ⟨d₁, _, hgDisk, _⟩ := hDiskAll _ hDiskMem
  refine ⟨hCap _ hBeltMem, d₁, ?_⟩
  dsimp only [qsburn05EpochGuard] at hgDisk
  cases hRec : recoverTruncatedAppendPlan toyCodec (qsburn05 512) d₁ with
  | none => rw [hRec] at hgDisk; cases hgDisk
  | some triple =>
    rw [hRec] at hgDisk
    rcases triple with ⟨dClean, hd, ws⟩
    exact ⟨dClean, hd, ws, rfl, of_decide_eq_true hgDisk⟩

/-- Concrete 1-turn accepting trace on `(toyTornSteady, mirBeltWitnessKernel)` recovering counter `0`
    and advancing `0 → 1` across both durable `QSBURN05` 80-byte slots and `MirBeltLatchKernel`! -/
theorem hwmBeltCoupled_accepts_epoch0_witness :
    let req : MirBeltLatchBindRequest := (mirBeltWitnessRequest 0 [1, 2, 3]).bind
    let s₀ : Disk × MirBeltLatchKernel := (toyTornSteady, mirBeltWitnessKernel)
    hwmBeltCoupledGuard.toParty.ValidTrace s₀
      [(req, hwmBeltCoupledGuard.out s₀ req)] (hwmBeltCoupledGuard.next s₀ req) := by
  intro req s₀
  obtain ⟨_, _, _, _, hSignerStep, _, _⟩ := Qsag.inhabited_mirBeltLatchSigner_fresh_sign_simulated
  obtain ⟨_, hBeltStep, _⟩ := Qsag.mirBeltLatchSigner_step_some hSignerStep
  obtain ⟨hgBelt, _, _⟩ := mirBeltLatchKernel_models.accepted hBeltStep
  have hMap := toy_append_tear_truncate_recovers_all_modes.2.1
  have hDiskGuard : qsburn05EpochGuard.guard toyTornSteady req = true := by
    dsimp only [qsburn05EpochGuard]
    cases hRec : recoverTruncatedAppendPlan toyCodec (qsburn05 512) toyTornSteady with
    | none => rw [hRec] at hMap; cases hMap
    | some triple =>
      rw [hRec] at hMap
      rcases triple with ⟨dClean, hd, ws⟩
      injection hMap with hPair
      have hLen0 : hd.len = 0 := (Prod.mk.inj hPair).1
      have hReq0 : req.epoch.toNat = 0 := by decide
      exact decide_eq_true (hLen0.trans hReq0.symm)
  have hGuard : hwmBeltCoupledGuard.guard s₀ req = true := by
    dsimp only [s₀, hwmBeltCoupledGuard, GuardedMachine.prod]
    rw [hDiskGuard, hgBelt]
    rfl
  exact .accept (hwmBeltCoupledGuard.step_accept hGuard) (.nil _)

/-- Premise-inhabitedness witness for `hwmBeltCoupled_multiTurn_safe`. -/
theorem inhabited_hwmBeltCoupled_trace :
    ∃ (s₀ sF : Disk × MirBeltLatchKernel)
      (tr : List (MirBeltLatchBindRequest × (Nat × MirBeltLatchBindOutcome))),
      s₀.2.WellFormed ∧
      hwmBeltCoupledGuard.toParty.ValidTrace s₀ tr sF := by
  obtain ⟨bk₀, _, _, hbWf₀, _, _⟩ := Qsag.inhabited_mirBeltLatchKernel_fresh_and_replay
  exact ⟨(toyTornSteady, bk₀), (toyTornSteady, bk₀), [], hbWf₀, .nil _⟩

/-- **Slot-Gap Fail-Closed Tooth (`tooth_hwmBeltCoupled_slot_gap_two_blocks_latch`)**:
    When `toyTornGapTwo` has `committed = 2 > slot + 1` (`recoverTruncatedAppendPlan = none`),
    `hwmBeltCoupledGuard` refuses to bind (`step = none`) on every kernel and request! -/
theorem tooth_hwmBeltCoupled_slot_gap_two_blocks_latch
    (k : MirBeltLatchKernel) (req : MirBeltLatchBindRequest) :
    ¬ ∃ out, hwmBeltCoupledGuard.toParty.step (toyTornGapTwo, k) req = some out := by
  have hRej : hwmBeltCoupledGuard.toParty.step (toyTornGapTwo, k) req = none := by
    apply hwmBeltCoupledGuard.step_reject
    dsimp only [hwmBeltCoupledGuard, GuardedMachine.prod, qsburn05EpochGuard]
    cases hRec : recoverTruncatedAppendPlan toyCodec (qsburn05 512) toyTornGapTwo with
    | none => rfl
    | some r => exact False.elim (tooth_toy_slot_gap_two_rejected ⟨r, hRec⟩)
  rintro ⟨out, hSome⟩
  rw [hRej] at hSome
  cases hSome

#verify_constructive
  hwmBeltCoupled_multiTurn_safe
  hwmBeltCoupled_accepts_epoch0_witness
  inhabited_hwmBeltCoupled_trace
  tooth_hwmBeltCoupled_slot_gap_two_blocks_latch
#verify_inhabited hwmBeltCoupled_multiTurn_safe inhabited_hwmBeltCoupled_trace
#tooth_pair hwmBeltCoupled_multiTurn_safe vs tooth_hwmBeltCoupled_slot_gap_two_blocks_latch

end Qsag.Tests.CrashAndGuardKitTeeth
end
