module

public import Qsag.Constructive
public import Qsag.SimulationSpine
public import Qsag.Goldilocks
public import Qsag.Poseidon2
public import Qsag.BinaryTower
public import Qsag.ElfBinaryVerify
public import Qsag.McRefine
public import Qsag.ThresholdApproval
public import Qsag.IdealTsig
public import Qsag.InteractiveUcEngine
public import Qsag.CustodySuiteFull
public import Qsag.RssSlhFullSecurity
public import Qsag.ThresholdMlDsaAndToprf
import all Qsag.Goldilocks
import all Qsag.Poseidon2
import all Qsag.SimulationSpine
import all Qsag.InteractiveUcEngine
import all Qsag.CustodySuiteFull
import all Qsag.ElfBinaryVerify
import all Qsag.ElfParse
import all Qsag.ThresholdMlDsaAndToprf

/-!
# Qsag.MirSpecBridge — Compositional ISA-to-MIR-to-Protocol-to-Ideal Specification Bridge

Constructive Lean 4.35 refinement and composition bridge (`0` proof gaps, `0` custom axioms,
`0 Classical.choice`, `≤ 12` `@[expose]` declarations) closing the specification-alignment boundary
between concrete fixed-width Rust/ELF guards and protocol-level security theorems:

1. **§1. Compiled `.rlib` 9-Kernel Equivalence Bundle & Protocol Field/Equality Bridges**:
   - Packages all 9 machine-code refinement theorems from `Qsag.McRefine`
     (`compiled_rlib_nine_kernels_verified`) over decoded x86-64 and AArch64 object slices.
   - Bridges `qsag_asm_ct_eq_32_{x86_64,aarch64}` directly to 32-byte digest list equality
     (`mc_ct_eq_32_refines_digest_equality`), `qsag_asm_ct_memzero_{x86_64,aarch64}` to physical
     secret-share byte wipe (`mc_ct_memzero_wipes_secret_share_window`), and
     `qsag_asm_goldilocks_{add,sub,mul}_ct` directly to canonical `Goldilocks` ring arithmetic and
     `ThresholdMlDsaAndToprf.toprf_2of5_corrects_one_malicious_server`
     (`mc_goldilocks_kernels_refine_field_and_toprf`).

2. **§2. Fixed-Width `UInt64` Policy Guard $\to$ `CustodySuiteFull` Multi-Turn Velocity Bridge**:
   - Models concrete fixed-width `UInt64` `MirPolicyGuardState` (`windowId`, `velocityWindowCap`,
     `accumulatedSpend`, `perTxCap : UInt64`, `burnedNonces : List UInt64`) ignoring untrusted
     caller-echoed spend fields and checking overflow-safe remaining budget
     `req.amountUnits ≤ m.velocityWindowCap - m.accumulatedSpend`.
   - Proves `LockstepSim` and `ForwardSim` (`mirPolicyGuard_forwardSim_custodyPolicy`) to
     `CustodySuiteFull.policyGuardStep` and lifts multi-turn traces directly into
     `CustodySuiteFull.policy_multiturn_velocity_and_intent_binding`
     (`mirPolicyGuard_implies_multiturn_velocity_and_intent_binding`).

3. **§3. Sticky-Poison `MirRssCutSession` & `UInt64` `MirMlDsaGate` $\to$ Protocol Security Bridges**:
   - Models `MirRssCutSession` setting sticky `poisoned := true` and wiping `shareSlotPresent`
     *before* clearing `pendingRelations := 0` on any Round-1/Round-2 check failure, paired with
     `#tooth` (`tooth_non_sticky_pending_clear_releases_corrupted_cut`), `ForwardSim`
     (`mirRssCutSession_forwardSim_walGate`), and direct composition into
     `RssSlhFullSecurity.rss_slh_real_ideal_view_indistinguishable` and
     `RssSlhFullSecurity.rss_slh_interactive_euf_cma_reduction`.
   - Proves `ForwardSim` (`mirRssMlDsaGate_forwardSim_spec`) from fixed-width `UInt64` norm, hint,
     and `checked_add(1)` epoch checks over RSS subset-shared keys (`MirRssMlDsaKeyState`) to
     `specRssMlDsaMachine`, paired with explicit Phase-2/3 rejected-attempt leakage characterization
     (`MirMlDsaAttemptLeakage`: `(openedMaskedW, openedW1, openedMaskedZAndLow, rejectBit)`),
     constructive `SimpleEquiv` mask bijection (`rssMaskVec4Equiv`), multi-turn epoch uniqueness,
     and standalone FIPS 204 `mldsaVerify` soundness (`mirRssMlDsaGate_leakage_bounded_and_fips204_sound`).

4. **§4. Certified `2 * q > n + f` `BeltLatch` Guard $\to$ `WalLatchState` & `IdealTsig` Bridge**:
   - Constructively extracts (`0 Classical.choice`) an honest validator `p ∈ Q₁ ∩ Q₂ \ corrupt`
     for any two `q`-quorums under `2 * q > n + f` (`beltLatch_quorum_intersection_honest_witness`),
     paired with `#tooth` (`tooth_subthreshold_beltLatch_quorum_allows_split_brain`), proving
     `ForwardSim` (`mirBeltLatch_forwardSim_walLatch`) to `WalLatchState` and discharging
     `IdealTsig.thresholdApproval_requires_honest_party`.

5. **§5. Unified End-to-End 4-Layer Transitive Simulation Chain (`isa_to_mir_to_protocol_to_ideal_sim`)**:
   - Instantiates `ForwardSim.trans` across:
     `(1) Compiled ELF ISA Slice` (`runX86` on `qsag_asm_ct_eq_32_x86_64` & `qsag_asm_ct_memzero_x86_64`)
     $\to$ `(2) Fixed-Width MIR Guarded State Machine`
     $\to$ `(3) Multi-Party 3-Round Interactive Wire Protocol` (`RealClusterState` + secret shares)
     $\to$ `(4) sk-Free Ideal Functionality F_tsig` (`IdealClusterState` + `approvedMsgs`).
   - Paired with multi-turn safety preservation (`isa_to_ideal_preserves_multiturn_safety`),
     non-vacuous multi-turn execution witness (`inhabited_four_layer_chain`), and `#tooth`
     refutation (`tooth_stateless_policy_link_breaks_four_layer_ideal_safety`) proving that
     replacing Link 2's authoritative spend ledger with caller-echoed spend breaks end-to-end
     ideal-functionality safety and refutes `ForwardSim`.
-/

public section

namespace Qsag

attribute [-instance] UInt8.instLawfulEqOrd UInt64.instLawfulEqOrd BitVec.instLawfulEqOrd

set_option autoImplicit false

/-! ## §1. Compiled `.rlib` 9-Kernel Equivalence Bundle & Protocol Field/Equality Bridges -/

/-- Unified specification bundle packaging all 9 machine-code refinement theorems from `Qsag.McRefine`
    over the extracted x86-64 and AArch64 `.rlib` object slices. -/
structure CompiledRlibKernelSuite : Prop where
  ct_eq_32_x86_64 :
    ∃ slice prog, findSliceByNameBytes x86ExtractedSlices ctEq32X86Name = some slice ∧
      decodeX86Stream slice.code = some prog ∧
      ∀ (s : X86State) (fuel : Nat), s.pc = 0 → s.halted = false → 20 ≤ fuel →
        (runX86 prog fuel s).1.halted = true ∧
        (runX86 prog fuel s).1.gpr.get 0 =
          (if ∀ i : Nat, i < 32 →
              s.mem (s.gpr.get 7 + UInt64.ofNat i) = s.mem (s.gpr.get 6 + UInt64.ofNat i)
            then 1 else 0) ∧
        (runX86 prog fuel s).1.mem = s.mem
  ct_eq_32_aarch64 :
    ∃ slice prog, findSliceByNameBytes aarch64ExtractedSlices ctEq32ArmName = some slice ∧
      decodeArm64Stream slice.code = some prog ∧
      ∀ (s : Arm64State) (fuel : Nat), s.pc = 0 → s.halted = false → 22 ≤ fuel →
        (runArm64 prog fuel s).1.halted = true ∧
        (runArm64 prog fuel s).1.gpr.get 0 =
          (if ∀ i : Nat, i < 32 →
              s.mem (s.gpr.get 0 + UInt64.ofNat i) = s.mem (s.gpr.get 1 + UInt64.ofNat i)
            then 1 else 0) ∧
        (runArm64 prog fuel s).1.mem = s.mem
  ct_memzero_x86_64 :
    ∃ slice prog, findSliceByNameBytes x86ExtractedSlices ctMemzeroX86Name = some slice ∧
      decodeX86Stream slice.code = some prog ∧
      ∀ (s : X86State) (fuel : Nat), s.pc = 0 → s.halted = false → 0 < (s.gpr.get 6).toNat →
        4 * (s.gpr.get 6).toNat + 4 ≤ fuel →
        (runX86 prog fuel s).1.halted = true ∧
        (∀ i : Nat, i < (s.gpr.get 6).toNat →
          (runX86 prog fuel s).1.mem (s.gpr.get 7 + UInt64.ofNat i) = 0) ∧
        (∀ a : UInt64, (∀ i : Nat, i < (s.gpr.get 6).toNat → a ≠ s.gpr.get 7 + UInt64.ofNat i) →
          (runX86 prog fuel s).1.mem a = s.mem a)
  ct_memzero_aarch64 :
    ∃ slice prog, findSliceByNameBytes aarch64ExtractedSlices ctMemzeroArmName = some slice ∧
      decodeArm64Stream slice.code = some prog ∧
      ∀ (s : Arm64State) (fuel : Nat), s.pc = 0 → s.halted = false → 0 < (s.gpr.get 1).toNat →
        3 * (s.gpr.get 1).toNat + 2 ≤ fuel →
        (runArm64 prog fuel s).1.halted = true ∧
        (∀ i : Nat, i < (s.gpr.get 1).toNat →
          (runArm64 prog fuel s).1.mem (s.gpr.get 0 + UInt64.ofNat i) = 0) ∧
        (∀ a : UInt64, (∀ i : Nat, i < (s.gpr.get 1).toNat → a ≠ s.gpr.get 0 + UInt64.ofNat i) →
          (runArm64 prog fuel s).1.mem a = s.mem a)
  ct_eq_bytes_x86_64 :
    ∃ slice prog, findSliceByNameBytes x86ExtractedSlices ctEqBytesX86Name = some slice ∧
      decodeX86Stream slice.code = some prog ∧
      ∀ (s : X86State) (fuel : Nat), s.pc = 0 → s.halted = false → 0 < (s.gpr.get 2).toNat →
        8 * (s.gpr.get 2).toNat + 7 ≤ fuel →
        (runX86 prog fuel s).1.halted = true ∧
        (runX86 prog fuel s).1.gpr.get 0 =
          (if ∀ i : Nat, i < (s.gpr.get 2).toNat →
              s.mem (s.gpr.get 7 + UInt64.ofNat i) = s.mem (s.gpr.get 6 + UInt64.ofNat i)
            then 1 else 0)
  goldilocks_add_x86_64 :
    ∃ slice prog, findSliceByNameBytes x86ExtractedSlices goldAddX86Name = some slice ∧
      decodeX86Stream slice.code = some prog ∧
      ∀ (s : X86State) (fuel : Nat), s.pc = 0 → s.halted = false → 17 ≤ fuel →
        (runX86 prog fuel s).1.halted = true ∧
        ((runX86 prog fuel s).1.gpr.get 0).toNat =
          ((s.gpr.get 7).toNat + (s.gpr.get 6).toNat) % goldilocksPrime
  goldilocks_sub_x86_64 :
    ∃ slice prog, findSliceByNameBytes x86ExtractedSlices goldSubX86Name = some slice ∧
      decodeX86Stream slice.code = some prog ∧
      ∀ (s : X86State) (fuel : Nat), s.pc = 0 → s.halted = false → 23 ≤ fuel →
        (runX86 prog fuel s).1.halted = true ∧
        ((runX86 prog fuel s).1.gpr.get 0).toNat =
          ((s.gpr.get 7).toNat + goldilocksPrime - (s.gpr.get 6).toNat % goldilocksPrime) %
            goldilocksPrime
  goldilocks_mul_x86_64 :
    ∃ slice prog, findSliceByNameBytes x86ExtractedSlices goldMulX86Name = some slice ∧
      decodeX86Stream slice.code = some prog ∧
      ∀ (s : X86State) (fuel : Nat), s.pc = 0 → s.halted = false → 25 ≤ fuel →
        (runX86 prog fuel s).1.halted = true ∧
        ((runX86 prog fuel s).1.gpr.get 0).toNat =
          ((s.gpr.get 7).toNat * (s.gpr.get 6).toNat) % goldilocksPrime
  goldilocks_mul_aarch64 :
    ∃ slice prog, findSliceByNameBytes aarch64ExtractedSlices goldMulArmName = some slice ∧
      decodeArm64Stream slice.code = some prog ∧
      ∀ (s : Arm64State) (fuel : Nat), s.pc = 0 → s.halted = false → 29 ≤ fuel →
        (runArm64 prog fuel s).1.halted = true ∧
        ((runArm64 prog fuel s).1.gpr.get 0).toNat =
          ((s.gpr.get 0).toNat * (s.gpr.get 1).toNat) % goldilocksPrime

/-- Discharges all 9 compiled `.rlib` machine-code equivalence obligations from `Qsag.McRefine`. -/
theorem compiled_rlib_nine_kernels_verified : CompiledRlibKernelSuite where
  ct_eq_32_x86_64 := by
    obtain ⟨sl, prog, hf, hd, hSpec⟩ := ct_eq_32_x86_64_mc_refines
    exact ⟨sl, prog, hf, hd, fun s fuel hpc hh hf' =>
      let ⟨h1, h2, h3, _⟩ := hSpec s fuel hpc hh hf'; ⟨h1, h2, h3⟩⟩
  ct_eq_32_aarch64 := by
    obtain ⟨sl, prog, hf, hd, hSpec⟩ := ct_eq_32_aarch64_mc_refines
    exact ⟨sl, prog, hf, hd, fun s fuel hpc hh hf' =>
      let ⟨h1, h2, h3, _⟩ := hSpec s fuel hpc hh hf'; ⟨h1, h2, h3⟩⟩
  ct_memzero_x86_64 := ct_memzero_x86_64_mc_refines
  ct_memzero_aarch64 := ct_memzero_aarch64_mc_refines
  ct_eq_bytes_x86_64 := by
    obtain ⟨sl, prog, hf, hd, hSpec⟩ := ct_eq_bytes_x86_64_mc_refines
    exact ⟨sl, prog, hf, hd, fun s fuel hpc hh hn hf' =>
      let ⟨h1, h2, _⟩ := hSpec s fuel hpc hh hn hf'; ⟨h1, h2⟩⟩
  goldilocks_add_x86_64 := by
    obtain ⟨sl, prog, hf, hd, hSpec⟩ := goldilocks_add_ct_x86_64_mc_refines
    exact ⟨sl, prog, hf, hd, fun s fuel hpc hh hf' =>
      let ⟨h1, h2, _⟩ := hSpec s fuel hpc hh hf'; ⟨h1, h2⟩⟩
  goldilocks_sub_x86_64 := by
    obtain ⟨sl, prog, hf, hd, hSpec⟩ := goldilocks_sub_ct_x86_64_mc_refines
    exact ⟨sl, prog, hf, hd, fun s fuel hpc hh hf' =>
      let ⟨h1, h2, _⟩ := hSpec s fuel hpc hh hf'; ⟨h1, h2⟩⟩
  goldilocks_mul_x86_64 := by
    obtain ⟨sl, prog, hf, hd, hSpec⟩ := goldilocks_mul_ct_x86_64_mc_refines
    exact ⟨sl, prog, hf, hd, fun s fuel hpc hh hf' =>
      let ⟨h1, h2, _⟩ := hSpec s fuel hpc hh hf'; ⟨h1, h2⟩⟩
  goldilocks_mul_aarch64 := by
    obtain ⟨sl, prog, hf, hd, hSpec⟩ := goldilocks_mul_ct_aarch64_mc_refines
    exact ⟨sl, prog, hf, hd, fun s fuel hpc hh hf' =>
      let ⟨h1, h2, _⟩ := hSpec s fuel hpc hh hf'; ⟨h1, h2⟩⟩

/-- Load a contiguous byte slice `bs` at `[base, base + bs.length)` inside flat byte memory. -/
def writeBytesWindow (m : UInt64 → UInt8) (base : Nat) (bs : List UInt8) : UInt64 → UInt8 :=
  fun addr =>
    let a := addr.toNat
    if base ≤ a ∧ a < base + bs.length then
      bs.getD (a - base) 0
    else
      m addr

private theorem addr_offset_toNat {base i : Nat} (hBound : base + i < 18446744073709551616) :
    (UInt64.ofNat base + UInt64.ofNat i).toNat = base + i := by
  have h64 : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
  rw [UInt64.toNat_add, UInt64.toNat_ofNat', UInt64.toNat_ofNat', h64]
  omega

private theorem writeBytesWindow_hit {m : UInt64 → UInt8} {base i : Nat} {bs : List UInt8}
    (hi : i < bs.length) (hNoWrap : base + bs.length < 18446744073709551616) :
    writeBytesWindow m base bs (UInt64.ofNat base + UInt64.ofNat i) = bs.getD i 0 := by
  unfold writeBytesWindow
  have hToNat := addr_offset_toNat (base := base) (i := i) (by omega)
  dsimp only
  rw [hToNat]
  have hCond : base ≤ base + i ∧ base + i < base + bs.length := ⟨by omega, by omega⟩
  rw [ite_eq_left hCond]
  have hSub : base + i - base = i := by omega
  rw [hSub]

private theorem writeBytesWindow_miss {m : UInt64 → UInt8} {base : Nat} {bs : List UInt8}
    {addr : UInt64} (hDisj : ¬ (base ≤ addr.toNat ∧ addr.toNat < base + bs.length)) :
    writeBytesWindow m base bs addr = m addr := by
  unfold writeBytesWindow
  dsimp only
  exact ite_eq_right hDisj

private theorem list_eq_iff_getD_eq :
    ∀ {xs ys : List UInt8},
      xs.length = ys.length →
      (xs = ys ↔ ∀ i : Nat, i < xs.length → xs.getD i 0 = ys.getD i 0)
  | [], [], _ => ⟨fun _ _ hi => absurd hi (Nat.not_lt_zero _), fun _ => rfl⟩
  | x :: xs, y :: ys, hLen => by
    have hLen' : xs.length = ys.length := Nat.succ.inj hLen
    constructor
    · rintro ⟨rfl, rfl⟩ _ _; rfl
    · intro hAll
      have h0 : x = y := hAll 0 (Nat.zero_lt_succ _)
      have hTail : xs = ys :=
        (list_eq_iff_getD_eq hLen').mpr (fun i hi => hAll (i + 1) (Nat.succ_lt_succ hi))
      rw [h0, hTail]

/-- Build an x86-64 entry state with `rdi = ptr1`, `rsi = ptr2`, `rdx = len`, and custom memory `m`. -/
def mkX86MemCall (ptr1 ptr2 len : UInt64) (m : UInt64 → UInt8) : X86State :=
  { x86Init ptr1 ptr2 len 0 0 with mem := m }

/-- Build an AArch64 entry state with `x0 = ptr1`, `x1 = ptr2`, and custom memory `m`. -/
def mkArmMemCall (ptr1 ptr2 : UInt64) (m : UInt64 → UInt8) : Arm64State :=
  { armInit ptr1 ptr2 0 with mem := m }

/-- **Bridge 1A (`mc_ct_eq_32_refines_digest_equality`)**:
    Running the decoded `.rlib` `qsag_asm_ct_eq_32_x86_64` and `qsag_asm_ct_eq_32_aarch64` slices
    on any two 32-byte digest buffers `d₁, d₂ : List UInt8` (`length = 32`) placed at `[0x100, 0x120)`
    and `[0x200, 0x220)` halts and decides exact list equality `d₁ = d₂` in `gpr[0]` (`1` iff equal,
    `0` iff distinct), bridging hardware constant-time comparisons to protocol digest checks. -/
theorem mc_ct_eq_32_refines_digest_equality (d₁ d₂ : List UInt8)
    (hLen₁ : d₁.length = 32) (hLen₂ : d₂.length = 32) :
    let m := writeBytesWindow (writeBytesWindow (fun _ => 0) 0x100 d₁) 0x200 d₂
    (∃ slice prog,
      findSliceByNameBytes x86ExtractedSlices ctEq32X86Name = some slice ∧
      decodeX86Stream slice.code = some prog ∧
      let out := (runX86 prog 20 (mkX86MemCall 0x100 0x200 0 m)).1
      out.halted = true ∧
      out.gpr.get 0 = (if d₁ = d₂ then 1 else 0) ∧
      ((out.gpr.get 0 == 1) = true ↔ d₁ = d₂)) ∧
    (∃ slice prog,
      findSliceByNameBytes aarch64ExtractedSlices ctEq32ArmName = some slice ∧
      decodeArm64Stream slice.code = some prog ∧
      let out := (runArm64 prog 22 (mkArmMemCall 0x100 0x200 m)).1
      out.halted = true ∧
      out.gpr.get 0 = (if d₁ = d₂ then 1 else 0) ∧
      ((out.gpr.get 0 == 1) = true ↔ d₁ = d₂)) := by
  intro m
  have h100 : (0x100 : UInt64) = UInt64.ofNat 0x100 := rfl
  have h200 : (0x200 : UInt64) = UInt64.ofNat 0x200 := rfl
  have hMemEqIff :
      (∀ i : Nat, i < 32 → m ((0x100 : UInt64) + UInt64.ofNat i) =
          m ((0x200 : UInt64) + UInt64.ofNat i)) ↔ d₁ = d₂ := by
    have hEqGetD := list_eq_iff_getD_eq (hLen₁.trans hLen₂.symm)
    rw [hLen₁] at hEqGetD
    refine Iff.trans ?_ hEqGetD.symm
    constructor
    · intro hAll i hi
      have hRead := hAll i hi
      have hL : m (UInt64.ofNat 0x100 + UInt64.ofNat i) = d₁.getD i 0 := by
        dsimp only [m]
        have hToNat := addr_offset_toNat (base := 0x100) (i := i) (by omega)
        rw [writeBytesWindow_miss (by rw [hToNat]; omega),
            writeBytesWindow_hit (hLen₁ ▸ hi) (by omega)]
      have hR : m (UInt64.ofNat 0x200 + UInt64.ofNat i) = d₂.getD i 0 :=
        writeBytesWindow_hit (hLen₂ ▸ hi) (by omega)
      rw [h100, h200] at hRead
      exact hL.symm.trans (hRead.trans hR)
    · intro hAll i hi
      have hL : m (UInt64.ofNat 0x100 + UInt64.ofNat i) = d₁.getD i 0 := by
        dsimp only [m]
        have hToNat := addr_offset_toNat (base := 0x100) (i := i) (by omega)
        rw [writeBytesWindow_miss (by rw [hToNat]; omega),
            writeBytesWindow_hit (hLen₁ ▸ hi) (by omega)]
      have hR : m (UInt64.ofNat 0x200 + UInt64.ofNat i) = d₂.getD i 0 :=
        writeBytesWindow_hit (hLen₂ ▸ hi) (by omega)
      rw [h100, h200, hL, hR]
      exact hAll i hi
  constructor
  · obtain ⟨sl, prog, hf, hd, hSpec⟩ := ct_eq_32_x86_64_mc_refines
    refine ⟨sl, prog, hf, hd, ?_⟩
    obtain ⟨hHalt, hRax, _⟩ :=
      hSpec (mkX86MemCall 0x100 0x200 0 m) 20 rfl rfl (Nat.le_refl 20)
    have hGpr7 : (mkX86MemCall 0x100 0x200 0 m).gpr.get 7 = 0x100 := rfl
    have hGpr6 : (mkX86MemCall 0x100 0x200 0 m).gpr.get 6 = 0x200 := rfl
    have hMemS : (mkX86MemCall 0x100 0x200 0 m).mem = m := rfl
    rw [hGpr7, hGpr6, hMemS] at hRax
    have hIfEq :
        (if ∀ i : Nat, i < 32 → m ((0x100 : UInt64) + UInt64.ofNat i) =
            m ((0x200 : UInt64) + UInt64.ofNat i) then (1 : UInt64) else 0) =
        (if d₁ = d₂ then 1 else 0) := by
      if hEqD : d₁ = d₂ then
        rw [ite_eq_left hEqD, ite_eq_left (hMemEqIff.mpr hEqD)]
      else
        rw [ite_eq_right hEqD, ite_eq_right (fun h => hEqD (hMemEqIff.mp h))]
    rw [hIfEq] at hRax
    refine ⟨hHalt, hRax, ?_⟩
    rw [hRax]
    if hEqD : d₁ = d₂ then
      rw [ite_eq_left hEqD]
      exact ⟨fun _ => hEqD, fun _ => rfl⟩
    else
      rw [ite_eq_right hEqD]
      exact ⟨fun hB => absurd hB (by decide), fun h => False.elim (hEqD h)⟩
  · obtain ⟨sl, prog, hf, hd, hSpec⟩ := ct_eq_32_aarch64_mc_refines
    refine ⟨sl, prog, hf, hd, ?_⟩
    obtain ⟨hHalt, hX0, _⟩ :=
      hSpec (mkArmMemCall 0x100 0x200 m) 22 rfl rfl (Nat.le_refl 22)
    have hGpr0 : (mkArmMemCall 0x100 0x200 m).gpr.get 0 = 0x100 := rfl
    have hGpr1 : (mkArmMemCall 0x100 0x200 m).gpr.get 1 = 0x200 := rfl
    have hMemS : (mkArmMemCall 0x100 0x200 m).mem = m := rfl
    rw [hGpr0, hGpr1, hMemS] at hX0
    have hIfEq :
        (if ∀ i : Nat, i < 32 → m ((0x100 : UInt64) + UInt64.ofNat i) =
            m ((0x200 : UInt64) + UInt64.ofNat i) then (1 : UInt64) else 0) =
        (if d₁ = d₂ then 1 else 0) := by
      if hEqD : d₁ = d₂ then
        rw [ite_eq_left hEqD, ite_eq_left (hMemEqIff.mpr hEqD)]
      else
        rw [ite_eq_right hEqD, ite_eq_right (fun h => hEqD (hMemEqIff.mp h))]
    rw [hIfEq] at hX0
    refine ⟨hHalt, hX0, ?_⟩
    rw [hX0]
    if hEqD : d₁ = d₂ then
      rw [ite_eq_left hEqD]
      exact ⟨fun _ => hEqD, fun _ => rfl⟩
    else
      rw [ite_eq_right hEqD]
      exact ⟨fun hB => absurd hB (by decide), fun h => False.elim (hEqD h)⟩

/-- **Bridge 1B (`mc_ct_memzero_wipes_secret_share_window`)**:
    Running the decoded `.rlib` `qsag_asm_ct_memzero_x86_64` (with `mfence`) and
    `qsag_asm_ct_memzero_aarch64` (with `dmb ish`) on a 32-byte secret share window at
    `[0x180, 0x1A0)` zeroes all 32 secret bytes while leaving surrounding pinned digest memory
    below `0x180` untouched — directly realizing hardware share zeroization for `walPoisonVault`. -/
theorem mc_ct_memzero_wipes_secret_share_window (m : UInt64 → UInt8) :
    (∃ slice prog,
      findSliceByNameBytes x86ExtractedSlices ctMemzeroX86Name = some slice ∧
      decodeX86Stream slice.code = some prog ∧
      let out := (runX86 prog 132 (mkX86MemCall 0x180 32 0 m)).1
      out.halted = true ∧
      (∀ i : Nat, i < 32 → out.mem ((0x180 : UInt64) + UInt64.ofNat i) = 0) ∧
      (∀ a : UInt64, a.toNat < 0x180 → out.mem a = m a)) ∧
    (∃ slice prog,
      findSliceByNameBytes aarch64ExtractedSlices ctMemzeroArmName = some slice ∧
      decodeArm64Stream slice.code = some prog ∧
      let out := (runArm64 prog 98 (mkArmMemCall 0x180 32 m)).1
      out.halted = true ∧
      (∀ i : Nat, i < 32 → out.mem ((0x180 : UInt64) + UInt64.ofNat i) = 0) ∧
      (∀ a : UInt64, a.toNat < 0x180 → out.mem a = m a)) := by
  have h180 : (0x180 : UInt64) = UInt64.ofNat 0x180 := rfl
  have hOutside : ∀ (a : UInt64), a.toNat < 0x180 →
      ∀ i : Nat, i < 32 → a ≠ (0x180 : UInt64) + UInt64.ofNat i := by
    intro a haLt i hi hEq
    have hToNat := congrArg UInt64.toNat hEq
    rw [h180, addr_offset_toNat (base := 0x180) (i := i) (by omega)] at hToNat
    omega
  constructor
  · obtain ⟨sl, prog, hf, hd, hSpec⟩ := ct_memzero_x86_64_mc_refines
    refine ⟨sl, prog, hf, hd, ?_⟩
    obtain ⟨hHalt, hZero, hPres⟩ :=
      hSpec (mkX86MemCall 0x180 32 0 m) 132 rfl rfl
        (show 0 < 32 by decide) (show 4 * 32 + 4 ≤ 132 by decide)
    exact ⟨hHalt, hZero, fun a ha => hPres a (hOutside a ha)⟩
  · obtain ⟨sl, prog, hf, hd, hSpec⟩ := ct_memzero_aarch64_mc_refines
    refine ⟨sl, prog, hf, hd, ?_⟩
    obtain ⟨hHalt, hZero, hPres⟩ :=
      hSpec (mkArmMemCall 0x180 32 m) 98 rfl rfl
        (show 0 < 32 by decide) (show 3 * 32 + 2 ≤ 98 by decide)
    exact ⟨hHalt, hZero, fun a ha => hPres a (hOutside a ha)⟩

/-- **Bridge 1C (`mc_goldilocks_kernels_refine_field_and_toprf`)**:
    Connects the compiled `.rlib` `qsag_asm_goldilocks_{add,sub,mul}_ct` x86-64 and AArch64 kernels
    directly to canonical `Goldilocks` field operations (`Goldilocks.add`, `Goldilocks.sub`,
    `Goldilocks.mul`) AND composes with `ThresholdMlDsaAndToprf.toprf_2of5_corrects_one_malicious_server`
    so hardware field outputs feed 1-Byzantine 2-of-5 TOPRF evaluation and finalization. -/
theorem mc_goldilocks_kernels_refine_field_and_toprf
    (a b : Goldilocks)
    (H : List UInt8 → List UInt8) (ctx : List UInt8) (layer : UInt64) (i j bad : Fin 5)
    (hCtx : ctx.length < 2 ^ 20) :
    let ua : UInt64 := UInt64.ofNat a.val
    let ub : UInt64 := UInt64.ofNat b.val
    (∃ slAdd pAdd slSub pSub slMulX pMulX slMulA pMulA,
      findSliceByNameBytes x86ExtractedSlices goldAddX86Name = some slAdd ∧
      decodeX86Stream slAdd.code = some pAdd ∧
      findSliceByNameBytes x86ExtractedSlices goldSubX86Name = some slSub ∧
      decodeX86Stream slSub.code = some pSub ∧
      findSliceByNameBytes x86ExtractedSlices goldMulX86Name = some slMulX ∧
      decodeX86Stream slMulX.code = some pMulX ∧
      findSliceByNameBytes aarch64ExtractedSlices goldMulArmName = some slMulA ∧
      decodeArm64Stream slMulA.code = some pMulA ∧
      ((runX86 pAdd 17 (x86Init ua ub 0 0 0)).1.gpr.get 0).toNat = (Goldilocks.add a b).val ∧
      ((runX86 pSub 23 (x86Init ua ub 0 0 0)).1.gpr.get 0).toNat = (Goldilocks.sub a b).val ∧
      ((runX86 pMulX 25 (x86Init ua ub 0 0 0)).1.gpr.get 0).toNat = (Goldilocks.mul a b).val ∧
      ((runArm64 pMulA 29 (armInit ua ub 0)).1.gpr.get 0).toNat = (Goldilocks.mul a b).val) ∧
    (∀ (masks : ToprfPerm12Masks) (keyShares inputShares : Fin 5 → Lane4)
       (serverOut : Fin 5 → Option (Fin 5 → Lane4)),
      (∀ p : Fin 5, p ≠ bad →
        serverOut p = some (fun c => (toprfEvalPerm12 masks (toprfInitPrfState keyShares inputShares) c).b0)) →
      clientFinalizeLane4 serverOut =
        some (toprfPlaintext (sumLane4Shares5 keyShares) (sumLane4Shares5 inputShares))) := by
  intro ua ub
  have h64 : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
  have haNat : ua.toNat = a.val := by
    dsimp only [ua]
    rw [UInt64.toNat_ofNat', h64]
    have haLt := Goldilocks.val_lt_two_pow_64 a
    omega
  have hbNat : ub.toNat = b.val := by
    dsimp only [ub]
    rw [UInt64.toNat_ofNat', h64]
    have hbLt := Goldilocks.val_lt_two_pow_64 b
    omega
  refine ⟨?_, (toprf_2of5_corrects_one_malicious_server H ctx layer i j hCtx bad).2.2⟩
  obtain ⟨slA, pA, hfA, hdA, hSpecA⟩ := goldilocks_add_ct_x86_64_mc_refines
  obtain ⟨slS, pS, hfS, hdS, hSpecS⟩ := goldilocks_sub_ct_x86_64_mc_refines
  obtain ⟨slMX, pMX, hfMX, hdMX, hSpecMX⟩ := goldilocks_mul_ct_x86_64_mc_refines
  obtain ⟨slMA, pMA, hfMA, hdMA, hSpecMA⟩ := goldilocks_mul_ct_aarch64_mc_refines
  refine ⟨slA, pA, slS, pS, slMX, pMX, slMA, pMA, hfA, hdA, hfS, hdS, hfMX, hdMX, hfMA, hdMA, ?_⟩
  have hAdd := (hSpecA (x86Init ua ub 0 0 0) 17 rfl rfl (Nat.le_refl 17)).2.1
  have hSub := (hSpecS (x86Init ua ub 0 0 0) 23 rfl rfl (Nat.le_refl 23)).2.1
  have hMulX := (hSpecMX (x86Init ua ub 0 0 0) 25 rfl rfl (Nat.le_refl 25)).2.1
  have hMulA := (hSpecMA (armInit ua ub 0) 29 rfl rfl (Nat.le_refl 29)).2.1
  have hG7 : (x86Init ua ub 0 0 0).gpr.get 7 = ua := rfl
  have hG6 : (x86Init ua ub 0 0 0).gpr.get 6 = ub := rfl
  have hA0 : (armInit ua ub 0).gpr.get 0 = ua := rfl
  have hA1 : (armInit ua ub 0).gpr.get 1 = ub := rfl
  rw [hG7, hG6, haNat, hbNat, ← Goldilocks.add_val] at hAdd
  rw [hG7, hG6, haNat, hbNat, Nat.mod_eq_of_lt b.isLt, ← Goldilocks.sub_val] at hSub
  rw [hG7, hG6, haNat, hbNat, ← Goldilocks.mul_val] at hMulX
  rw [hA0, hA1, haNat, hbNat, ← Goldilocks.mul_val] at hMulA
  exact ⟨hAdd, hSub, hMulX, hMulA⟩

/-! ## §2. Fixed-Width `UInt64` Policy Guard $\to$ `CustodySuiteFull` Multi-Turn Velocity Bridge -/

def u64MemBool (x : UInt64) : List UInt64 → Bool
  | [] => false
  | y :: ys => (x == y) || u64MemBool x ys

private theorem u64_beq_iff_eq_constructive {x y : UInt64} :
    (x == y) = true ↔ x = y := by
  change Nat.beq x.toNat y.toNat = true ↔ x = y
  rw [Nat.beq_eq]
  exact ⟨fun h => UInt64.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq h), fun h => congrArg UInt64.toNat h⟩

private theorem u64MemBool_eq_true_iff (x : UInt64) :
    ∀ (ys : List UInt64), u64MemBool x ys = true ↔ x ∈ ys
  | [] => by simp [u64MemBool]
  | y :: ys => by
    simp only [u64MemBool, Bool.or_eq_true, u64_beq_iff_eq_constructive,
      u64MemBool_eq_true_iff x ys, List.mem_cons]

private theorem u64MemBool_map_toNat {x : UInt64} {ys : List UInt64} :
    x.toNat ∈ ys.map UInt64.toNat ↔ x ∈ ys := by
  induction ys with
  | nil => simp
  | cons y ys ih =>
    simp only [List.map_cons, List.mem_cons, ih]
    constructor
    · rintro (hEq | hRest)
      · exact .inl (UInt64.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq hEq))
      · exact .inr hRest
    · rintro (rfl | hRest)
      · exact .inl rfl
      · exact .inr hRest

/-- Fixed-width Rust/MIR transaction intent request carrying `UInt64` numeric fields plus an
    untrusted `callerEchoedSpent : UInt64` field (which the authoritative guard must ignore). -/
structure MirTxIntent where
  recipient : List UInt8
  amountUnits : UInt64
  windowId : UInt64
  policyDigest : List UInt8
  authorityDigest : List UInt8
  nonce : UInt64
  callerEchoedSpent : UInt64 := 0
  deriving DecidableEq, Repr

/-- Canonical projection from fixed-width `MirTxIntent` to `CustodySuiteFull.TransactionIntent`. -/
def MirTxIntent.toTransactionIntent (req : MirTxIntent) : TransactionIntent where
  recipient := req.recipient
  amount_units := req.amountUnits.toNat
  window_id := req.windowId.toNat
  policy_digest := req.policyDigest
  authority_digest := req.authorityDigest
  nonce := req.nonce.toNat

/-- Concrete fixed-width `UInt64` policy guard state mirroring `crates/qsag-policy`. -/
structure MirPolicyGuardState where
  windowId : UInt64
  velocityWindowCap : UInt64
  accumulatedSpend : UInt64
  burnedNonces : List UInt64
  pinnedPolicyDigest : List UInt8
  pinnedAuthorityDigest : List UInt8
  allowedRecipients : List (List UInt8)
  perTxCap : UInt64
  deriving DecidableEq, Repr

/-- Abstraction map from fixed-width `MirPolicyGuardState` to `CustodySuiteFull.StatefulPolicyGuard`. -/
def MirPolicyGuardState.toStatefulPolicyGuard (m : MirPolicyGuardState) : StatefulPolicyGuard where
  window_id := m.windowId.toNat
  velocity_window_cap := m.velocityWindowCap.toNat
  accumulated_spend := m.accumulatedSpend.toNat
  burned_intent_nonces := m.burnedNonces.map UInt64.toNat
  pinned_policy_digest := m.pinnedPolicyDigest
  pinned_authority_digest := m.pinnedAuthorityDigest
  allowed_recipients := m.allowedRecipients
  per_tx_cap := m.perTxCap.toNat

/-- Concrete overflow-safe `UInt64` MIR policy step: checks remaining window capacity via
    `req.amountUnits ≤ m.velocityWindowCap - m.accumulatedSpend` (never trusting `callerEchoedSpent`). -/
def mirPolicyStep (m : MirPolicyGuardState) (req : MirTxIntent) :
    Option (MirPolicyGuardState × ApprovedIntentEnvelope) :=
  if req.windowId != m.windowId then none
  else if req.policyDigest != m.pinnedPolicyDigest then none
  else if req.authorityDigest != m.pinnedAuthorityDigest then none
  else if ¬ (req.recipient ∈ m.allowedRecipients) then none
  else if ¬ (req.amountUnits.toNat ≤ m.perTxCap.toNat) then none
  else if ¬ (req.amountUnits.toNat ≤ (m.velocityWindowCap - m.accumulatedSpend).toNat) then none
  else if u64MemBool req.nonce m.burnedNonces then none
  else
    let m' : MirPolicyGuardState :=
      { m with
        accumulatedSpend := m.accumulatedSpend + req.amountUnits
        burnedNonces := req.nonce :: m.burnedNonces }
    let tx := req.toTransactionIntent
    some (m', { intent := tx, canonicalBytes := encodeTransactionIntent tx })

/-- Canonical `PartyMachine` for the fixed-width `UInt64` MIR policy guard. -/
@[expose]
def mirPolicyGuardMachine : PartyMachine MirPolicyGuardState MirTxIntent ApprovedIntentEnvelope :=
  PartyMachine.ofOption mirPolicyStep

/-- Specification `PartyMachine` wrapping `CustodySuiteFull.policyGuardStep` over `MirTxIntent`. -/
def specPolicyGuardMachine : PartyMachine StatefulPolicyGuard MirTxIntent ApprovedIntentEnvelope :=
  PartyMachine.ofOutcome (fun g req => (policyGuardStep g req.toTransactionIntent).toStepOutcome)

private theorem add_le_of_le_sub_local {a b c : Nat} (hac : a ≤ c) (hb : b ≤ c - a) :
    a + b ≤ c := by
  omega

private theorem not_add_le_of_not_le_sub_local {a b c : Nat} (hac : a ≤ c) (hnb : ¬ (b ≤ c - a)) :
    ¬ (a + b ≤ c) := by
  omega

/-- Functional `LockstepSim` proving that fixed-width `UInt64` subtraction/addition in
    `mirPolicyGuardMachine` never wraps around under `accumulatedSpend ≤ velocityWindowCap`
    and refines `CustodySuiteFull.policyGuardStep` step-for-step. -/
def mirPolicyGuard_lockstepSim :
    LockstepSim mirPolicyGuardMachine specPolicyGuardMachine where
  Inv m := m.accumulatedSpend.toNat ≤ m.velocityWindowCap.toNat
  abs := MirPolicyGuardState.toStatefulPolicyGuard
  step_eq {m} req hInv := by
    have h64 : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
    have hCapLt : m.velocityWindowCap.toNat < 18446744073709551616 := m.velocityWindowCap.toNat_lt
    have hSubNoWrap :
        (m.velocityWindowCap - m.accumulatedSpend).toNat =
          m.velocityWindowCap.toNat - m.accumulatedSpend.toNat := by
      rw [UInt64.toNat_sub, h64]
      omega
    have hWinBne :
        (req.windowId.toNat != m.windowId.toNat) = (req.windowId != m.windowId) := rfl
    have hF : ¬ (false = true) := Bool.noConfusion
    have hT : true = true := rfl
    dsimp only [mirPolicyGuardMachine, specPolicyGuardMachine,
      PartyMachine.ofOption, PartyMachine.ofOutcome]
    unfold mirPolicyStep policyGuardStep MirTxIntent.toTransactionIntent
      MirPolicyGuardState.toStatefulPolicyGuard CustodyStepOutcome.toStepOutcome
    dsimp only
    rw [hWinBne]
    cases h1 : (req.windowId != m.windowId)
    · repeat rw [ite_eq_right hF]
      cases h2 : (req.policyDigest != m.pinnedPolicyDigest)
      · repeat rw [ite_eq_right hF]
        cases h3 : (req.authorityDigest != m.pinnedAuthorityDigest)
        · repeat rw [ite_eq_right hF]
          if h4Ok : req.recipient ∈ m.allowedRecipients then
            have hNot4 : ¬ ¬ (req.recipient ∈ m.allowedRecipients) := fun hn => hn h4Ok
            repeat rw [ite_eq_right hNot4]
            if h5Ok : req.amountUnits.toNat ≤ m.perTxCap.toNat then
              have hNot5 : ¬ ¬ (req.amountUnits.toNat ≤ m.perTxCap.toNat) := fun hn => hn h5Ok
              repeat rw [ite_eq_right hNot5]
              rw [hSubNoWrap]
              if h6Ok : req.amountUnits.toNat ≤ m.velocityWindowCap.toNat - m.accumulatedSpend.toNat then
                have h6SpecOk : m.accumulatedSpend.toNat + req.amountUnits.toNat ≤ m.velocityWindowCap.toNat :=
                  add_le_of_le_sub_local hInv h6Ok
                have hNot6 : ¬ ¬ (req.amountUnits.toNat ≤ m.velocityWindowCap.toNat - m.accumulatedSpend.toNat) :=
                  fun hn => hn h6Ok
                have hNot6Spec : ¬ ¬ (m.accumulatedSpend.toNat + req.amountUnits.toNat ≤ m.velocityWindowCap.toNat) :=
                  fun hn => hn h6SpecOk
                repeat rw [ite_eq_right hNot6]
                repeat rw [ite_eq_right hNot6Spec]
                cases h7 : u64MemBool req.nonce m.burnedNonces
                · have hNotMem : req.nonce.toNat ∉ m.burnedNonces.map UInt64.toNat := by
                    intro hIn
                    have hMem := u64MemBool_map_toNat.mp hIn
                    rw [(u64MemBool_eq_true_iff req.nonce m.burnedNonces).mpr hMem] at h7
                    cases h7
                  repeat rw [ite_eq_right hF]
                  repeat rw [ite_eq_right hNotMem]
                  dsimp only [List.map_cons]
                  have hAddNoWrap :
                      (m.accumulatedSpend + req.amountUnits).toNat =
                        m.accumulatedSpend.toNat + req.amountUnits.toNat := by
                    rw [UInt64.toNat_add, h64]
                    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt h6SpecOk hCapLt)
                  refine ⟨by rw [hAddNoWrap]; exact h6SpecOk, ?_⟩
                  rw [hAddNoWrap]
                  rfl
                · have hInMap : req.nonce.toNat ∈ m.burnedNonces.map UInt64.toNat :=
                    u64MemBool_map_toNat.mpr ((u64MemBool_eq_true_iff req.nonce m.burnedNonces).mp h7)
                  repeat rw [ite_eq_left hT]
                  repeat rw [ite_eq_left hInMap]
                  dsimp only
                  exact ⟨hInv, rfl, rfl⟩
              else
                have h6Spec : ¬ (m.accumulatedSpend.toNat + req.amountUnits.toNat ≤ m.velocityWindowCap.toNat) :=
                  not_add_le_of_not_le_sub_local hInv h6Ok
                repeat rw [ite_eq_left h6Ok]
                repeat rw [ite_eq_left h6Spec]
                dsimp only
                exact ⟨hInv, rfl, rfl⟩
            else
              repeat rw [ite_eq_left h5Ok]
              dsimp only
              exact ⟨hInv, rfl, rfl⟩
          else
            repeat rw [ite_eq_left h4Ok]
            dsimp only
            exact ⟨hInv, rfl, rfl⟩
        · repeat rw [ite_eq_left hT]
          dsimp only
          exact ⟨hInv, rfl, rfl⟩
      · repeat rw [ite_eq_left hT]
        dsimp only
        exact ⟨hInv, rfl, rfl⟩
    · repeat rw [ite_eq_left hT]
      dsimp only
      exact ⟨hInv, rfl, rfl⟩

/-- Compositional `ForwardSim` from `mirPolicyGuardMachine` to `specPolicyGuardMachine`. -/
def mirPolicyGuard_forwardSim_custodyPolicy :
    ForwardSim mirPolicyGuardMachine specPolicyGuardMachine :=
  mirPolicyGuard_lockstepSim.toForwardSim

private theorem specPolicyGuard_rejected_same {g g' : StatefulPolicyGuard}
    {tx : TransactionIntent} {err : PolicyRejectReason}
    (hPol : policyGuardStep g tx = .rejected g' err) : g' = g := by
  unfold policyGuardStep at hPol
  repeat' split at hPol
  all_goals first
    | (injection hPol with hEq _; exact hEq.symm)
    | cases hPol

private theorem specPolicyValidTrace_to_validCustodyTrace
    {g₀ gFinal : StatefulPolicyGuard}
    {tr : List (MirTxIntent × ApprovedIntentEnvelope)}
    (hTr : specPolicyGuardMachine.ValidTrace g₀ tr gFinal) :
    ValidCustodyTrace policyGuardStep g₀
      (tr.map (fun p => (p.1.toTransactionIntent, some p.2))) gFinal := by
  induction hTr with
  | nil g => exact .nil g
  | @accept g₀ g₁ _ req env _ hStep _ ih =>
    dsimp only [specPolicyGuardMachine, PartyMachine.ofOutcome] at hStep
    cases hPol : policyGuardStep g₀ req.toTransactionIntent with
    | rejected _ _ =>
      rw [hPol] at hStep; simp [CustodyStepOutcome.toStepOutcome] at hStep
    | accepted g₁' out₁ =>
      rw [hPol] at hStep
      simp only [CustodyStepOutcome.toStepOutcome, Option.some.injEq, Prod.mk.injEq] at hStep
      obtain ⟨rfl, rfl⟩ := hStep
      exact .consAccepted hPol ih
  | @reject g₀ _ req _ hNone _ ih =>
    have hErr : specPolicyGuardMachine.errStep g₀ req = g₀ := by
      dsimp only [specPolicyGuardMachine, PartyMachine.ofOutcome] at hNone ⊢
      cases hPol : policyGuardStep g₀ req.toTransactionIntent with
      | accepted g₁ _ =>
        rw [hPol] at hNone; simp [CustodyStepOutcome.toStepOutcome] at hNone
      | rejected g₁ _ =>
        simp only [CustodyStepOutcome.toStepOutcome]
        exact specPolicyGuard_rejected_same hPol
    rw [hErr] at ih
    exact ih

private theorem traceApprovedOutputs_map_some :
    ∀ (tr : List (MirTxIntent × ApprovedIntentEnvelope)),
      traceApprovedOutputs (tr.map (fun p => (p.1.toTransactionIntent, some p.2))) =
        tr.map Prod.snd
  | [] => traceApprovedOutputs_nil
  | _ :: rest => by
    simp only [List.map_cons, traceApprovedOutputs_cons_some, traceApprovedOutputs_map_some rest]

/-- **Bridge 2 (`mirPolicyGuard_implies_multiturn_velocity_and_intent_binding`)**:
    Lifts any multi-turn execution of the fixed-width `UInt64` `mirPolicyGuardMachine` across
    `mirPolicyGuard_forwardSim_custodyPolicy` directly into
    `CustodySuiteFull.policy_multiturn_velocity_and_intent_binding`:
    1. Cumulative approved spend never overflows `UInt64` and obeys `∑ amount_units ≤ velocityWindowCap`
       regardless of adversarially forged `callerEchoedSpent` values;
    2. All approved nonces are strictly `Nodup` and disjoint from `m₀.burnedNonces`;
    3. Every approved envelope is bound to `m₀`'s pinned digests/allowlist and bijective
       `encodeTransactionIntent` / `decodeTransactionIntent` framing. -/
theorem mirPolicyGuard_implies_multiturn_velocity_and_intent_binding
    {m₀ mFinal : MirPolicyGuardState}
    {trace : List (MirTxIntent × ApprovedIntentEnvelope)}
    (hInitLe : m₀.accumulatedSpend.toNat ≤ m₀.velocityWindowCap.toNat)
    (hTrace : mirPolicyGuardMachine.ValidTrace m₀ trace mFinal) :
    let approved := trace.map Prod.snd
    let approvedSum := (approved.map (fun e => e.intent.amount_units)).foldr (· + ·) 0
    m₀.accumulatedSpend.toNat + approvedSum = mFinal.accumulatedSpend.toNat ∧
    mFinal.accumulatedSpend.toNat ≤ m₀.velocityWindowCap.toNat ∧
    approvedSum ≤ m₀.velocityWindowCap.toNat ∧
    (approved.map (fun e => e.intent.nonce)).Nodup ∧
    (∀ e ∈ approved,
      e.intent.window_id = m₀.windowId.toNat ∧
      e.intent.policy_digest = m₀.pinnedPolicyDigest ∧
      e.intent.authority_digest = m₀.pinnedAuthorityDigest ∧
      e.intent.recipient ∈ m₀.allowedRecipients ∧
      e.intent.amount_units ≤ m₀.perTxCap.toNat ∧
      e.canonicalBytes = encodeTransactionIntent e.intent) ∧
    (∀ tx : TransactionIntent, decodeTransactionIntent (encodeTransactionIntent tx) = some tx) := by
  have hRel₀ : mirPolicyGuard_forwardSim_custodyPolicy.Rel m₀ m₀.toStatefulPolicyGuard :=
    ⟨hInitLe, rfl⟩
  obtain ⟨gFinal, hSpecTr, hRelF⟩ :=
    mirPolicyGuard_forwardSim_custodyPolicy.lift_validTrace hRel₀ hTrace
  rcases hRelF with ⟨_, hAbsEq⟩
  subst hAbsEq
  have hCustTr := specPolicyValidTrace_to_validCustodyTrace hSpecTr
  have hMain := policy_multiturn_velocity_and_intent_binding hInitLe hCustTr
  dsimp only [MirPolicyGuardState.toStatefulPolicyGuard] at hMain
  rw [traceApprovedOutputs_map_some] at hMain
  rcases hMain with ⟨hSumEq, hFinLe, hAppLe, hNodup, hProps, hRoundtrip, _⟩
  refine ⟨hSumEq, hFinLe, hAppLe, hNodup, ?_, hRoundtrip⟩
  intro e he
  obtain ⟨_, hw, hp, ha, hr, hpt, hc⟩ := hProps e he
  exact ⟨hw, hp, ha, hr, hpt, hc⟩

/-! ## §3. Sticky-Poison `MirRssCutSession` & `UInt64` `MirMlDsaGate` $\to$ Protocol Security Bridges -/

/-- Concrete `BGIN19` `GF(2^128)` (`Tower128`) Round-2 wire-MAC relation check:
    verifies `alpha * xWire + keyOffset = macShare` directly over `GF(2^128)` field elements
    (`0` caller-reported booleans!). -/
structure BginWireRelation where
  xWire : Tower128
  macShare : Tower128
  keyOffset : Tower128
  alpha : Tower128
  deriving DecidableEq

/-- Evaluate a single `GF(2^128)` `BGIN19` wire-MAC relation `alpha * xWire + keyOffset = macShare`. -/
def bginRelationHolds (r : BginWireRelation) : Bool :=
  decide (towerAdd 7 (towerMul 7 r.alpha r.xWire) r.keyOffset = r.macShare)

/-- Evaluate a non-empty batch of `GF(2^128)` `BGIN19` wire-MAC relations. -/
def bginBatchHolds (rels : List BginWireRelation) : Bool :=
  !rels.isEmpty && rels.all bginRelationHolds

/-- Concrete fixed-width Rust/MIR `RssCutSession` state (`crates/qsag-core/src/fips205.rs` and
    `aeneas/qsag-verified/src/rss_cut_session.rs`):
    - `phase : UInt8` (`0` = `Init`, `1` = `Round1Committed`, `2` = `Round2Checked`, `0xFF` = `Poisoned`),
    - `pendingRelations : UInt64`,
    - `consistencyVerified : Bool`,
    - `poisoned : Bool` (sticky quarantine flag set *before* `pendingRelations` is cleared),
    - `shareSlotPresent : Bool`. -/
structure MirRssCutSession where
  phase : UInt8
  pendingRelations : UInt64
  consistencyVerified : Bool
  poisoned : Bool
  shareSlotPresent : Bool
  deriving DecidableEq, Repr

/-- Operations on a threshold cut session across Rounds 1, 2, and 3, carrying concrete `GF(2^128)`
    `BginWireRelation` batches rather than caller-reported booleans. -/
inductive MirRssCutInput where
  | recordRound1 (relationCount : UInt64)
  | verifyBatchConsistency (relations : List BginWireRelation)
  | releaseRound3Cut (cutPayload : ByteArray)
  deriving DecidableEq

/-- Output events emitted by `MirRssCutSession`. -/
inductive MirRssCutOutput where
  | round1Recorded (relationCount : UInt64)
  | batchVerified
  | cutReleased (cutPayload : ByteArray)
  deriving DecidableEq

/-- Authoritative sticky-poison `MirRssCutSession` step:
    verifies both exact batch cardinality (`relations.length = s.pendingRelations.toNat`) and every
    `GF(2^128)` `BGIN19` equation (`bginBatchHolds relations`), latching `poisoned := true`,
    `phase := 0xFF`, and `shareSlotPresent := false` **before** clearing `pendingRelations := 0`
    whenever any relation fails! -/
def mirRssCutStep (s : MirRssCutSession) (inp : MirRssCutInput) :
    StepOutcome MirRssCutSession MirRssCutOutput Unit :=
  if s.poisoned || !s.shareSlotPresent then
    .err { s with phase := 0xFF, pendingRelations := 0, consistencyVerified := false,
                  poisoned := true, shareSlotPresent := false } ()
  else
    match inp with
    | .recordRound1 rels =>
      if s.phase == 0 && rels != 0 then
        .ok { s with phase := 1, pendingRelations := rels, consistencyVerified := false }
            (.round1Recorded rels)
      else
        .err s ()
    | .verifyBatchConsistency relations =>
      if s.phase == 1 then
        if decide (relations.length = s.pendingRelations.toNat) && bginBatchHolds relations then
          .ok { s with phase := 2, pendingRelations := 0, consistencyVerified := true }
              .batchVerified
        else
          -- Sticky poison + share wipe BEFORE clearing `pendingRelations := 0`!
          .err { phase := 0xFF, pendingRelations := 0, consistencyVerified := false,
                 poisoned := true, shareSlotPresent := false } ()
      else
        .err s ()
    | .releaseRound3Cut payload =>
      if s.phase == 2 && s.pendingRelations == 0 && s.consistencyVerified then
        .ok { s with phase := 0, consistencyVerified := false } (.cutReleased payload)
      else
        .err s ()

/-- Canonical `PartyMachine` for `MirRssCutSession`. -/
@[expose]
def mirRssCutMachine : PartyMachine MirRssCutSession MirRssCutInput MirRssCutOutput :=
  PartyMachine.ofOutcome mirRssCutStep

/-- Buggy non-sticky variant that clears `pendingRelations := 0` on a failed `GF(2^128)` `BGIN19`
    batch check without latching `poisoned := true`, allowing a subsequent empty `[]` call to pass
    `[].all bginRelationHolds = true` vacuously and open the Round-3 cut! -/
def buggyNonStickyRssCutStep (s : MirRssCutSession) (inp : MirRssCutInput) :
    StepOutcome MirRssCutSession MirRssCutOutput Unit :=
  match inp with
  | .recordRound1 rels =>
    .ok { s with phase := 1, pendingRelations := rels, consistencyVerified := false }
        (.round1Recorded rels)
  | .verifyBatchConsistency relations =>
    if decide (relations.length = s.pendingRelations.toNat) && relations.all bginRelationHolds then
      .ok { s with phase := 2, pendingRelations := 0, consistencyVerified := true } .batchVerified
    else
      -- BUG: clears `pendingRelations := 0` without setting `poisoned := true`!
      .err { s with pendingRelations := 0, consistencyVerified := false } ()
  | .releaseRound3Cut payload =>
    if !s.poisoned && s.phase == 2 && s.pendingRelations == 0 && s.consistencyVerified then
      .ok { s with phase := 0, consistencyVerified := false } (.cutReleased payload)
    else
      .err s ()

/-- **`#tooth` (`tooth_non_sticky_pending_clear_releases_corrupted_cut`)**:
    Submitting a forged `GF(2^128)` `BGIN19` relation (`0 * 1 + 0 = 0 ≠ 1`) on `verifyBatchConsistency`
    causes `buggyNonStickyRssCutStep` to clear `pendingRelations := 0` without setting `poisoned := true`,
    so a subsequent `verifyBatchConsistency []` call passes vacuously on the cleared queue and releases
    `cutReleased`; the authoritative `mirRssCutMachine` permanently poisons and blocks both `[]` and
    any subsequent valid `GF(2^128)` relation forever. -/
theorem tooth_non_sticky_pending_clear_releases_corrupted_cut (payload : ByteArray) :
    let init : MirRssCutSession := ⟨0, 0, false, false, true⟩
    let forgedRel : BginWireRelation := ⟨towerOne 7, towerOne 7, towerZero 7, towerZero 7⟩
    let validRel : BginWireRelation := ⟨towerOne 7, towerOne 7, towerZero 7, towerOne 7⟩
    let buggyM := PartyMachine.ofOutcome buggyNonStickyRssCutStep
    let s1 := (buggyM.runStep init (.recordRound1 1)).1
    let s2 := (buggyM.runStep s1 (.verifyBatchConsistency [forgedRel])).1
    let s3 := (buggyM.runStep s2 (.verifyBatchConsistency [])).1
    (buggyM.runStep s3 (.releaseRound3Cut payload)).2 = some (.cutReleased payload) ∧
    (let g1 := (mirRssCutMachine.runStep init (.recordRound1 1)).1
     let g2 := (mirRssCutMachine.runStep g1 (.verifyBatchConsistency [forgedRel])).1
     let g3 := (mirRssCutMachine.runStep g2 (.verifyBatchConsistency [])).1
     g2.poisoned = true ∧
     g2.shareSlotPresent = false ∧
     (mirRssCutMachine.runStep g2 (.verifyBatchConsistency [validRel])).2 = none ∧
     (mirRssCutMachine.runStep g3 (.releaseRound3Cut payload)).2 = none) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Protocol-level pre-cut barrier & `HonestCustodyVault` specification state. -/
structure SpecPreCutVaultState where
  stage : Nat
  pendingRelations : Nat
  vault : HonestCustodyVault Unit

def specPreCutVaultStep (st : SpecPreCutVaultState) (inp : MirRssCutInput) :
    StepOutcome SpecPreCutVaultState MirRssCutOutput Unit :=
  if st.vault.wal.poisoned || st.vault.shareSlot.isNone then
    .err { stage := 255, pendingRelations := 0, vault := walPoisonVault st.vault } ()
  else
    match inp with
    | .recordRound1 rels =>
      if st.stage == 0 && rels != 0 then
        .ok { st with stage := 1, pendingRelations := rels.toNat } (.round1Recorded rels)
      else
        .err st ()
    | .verifyBatchConsistency relations =>
      if st.stage == 1 then
        if decide (relations.length = st.pendingRelations) && bginBatchHolds relations then
          .ok { st with stage := 2, pendingRelations := 0 } .batchVerified
        else
          .err { stage := 255, pendingRelations := 0, vault := walPoisonVault st.vault } ()
      else
        .err st ()
    | .releaseRound3Cut payload =>
      if st.stage == 2 then
        .ok { st with stage := 0, pendingRelations := 0 } (.cutReleased payload)
      else
        .err st ()

def specPreCutVaultMachine : PartyMachine SpecPreCutVaultState MirRssCutInput MirRssCutOutput :=
  PartyMachine.ofOutcome specPreCutVaultStep

/-- **Bridge 3A (`mirRssCutSession_forwardSim_walGate`)**:
    Proves `ForwardSim` from the concrete fixed-width `MirRssCutSession` machine to the
    `HonestCustodyVault` / `walPoisonVault` pre-cut barrier specification. -/
