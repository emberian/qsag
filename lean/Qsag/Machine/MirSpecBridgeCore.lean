module
import all Qsag.Math.GoldilocksBase

public import Qsag.Tactic.Prelude
public import Qsag.Exec.SimulationSpine
public import Qsag.Math.Goldilocks
public import Qsag.Oracle.Poseidon2
public import Qsag.Math.Gf2Pow128
public import Qsag.Machine.ElfBinaryVerify
public import Qsag.Machine.McRefine
public import Qsag.Protocol.Threshold.ThresholdApproval
public import Qsag.Protocol.Threshold.IdealTsig
public import Qsag.Exec.InteractiveUcEngine
public import Qsag.Custody.CustodySuiteFull
public import Qsag.Protocol.Threshold.RssSlhFullSecurity
public import Qsag.Protocol.Threshold.ThresholdMlDsaAndToprf
import all Qsag.Math.CoeffPoly
import all Qsag.Math.Goldilocks
import all Qsag.Oracle.Poseidon2
import all Qsag.Exec.SimulationSpine
import all Qsag.Exec.InteractiveUcEngine
import all Qsag.Protocol.Threshold.RssSlhFullSecurity
import all Qsag.Custody.CustodySuiteFull
import all Qsag.Machine.ElfBinaryVerify
import all Qsag.Machine.ElfParse
import all Qsag.Protocol.Threshold.ThresholdMlDsaAndToprf
import Qsag.Tactic.AssuranceKit

/-!
# Qsag.Machine.MirSpecBridge — fixed-width guard models and their composition into the protocol specs

## What this file is and is not

Every `Mir*` structure and machine in this file is a **hand-written Lean model**. The `qsag`
package does not import the Aeneas extraction (`aeneas/lean`, package `qsag_aeneas`), because the
package dependency runs the other way (`qsag_aeneas` depends on `qsag`); therefore no declaration
here mentions `QsagVerified.Funs` directly, and cross-package extraction welds live in
`aeneas/lean/QsagVerified/Proofs/AuthenticatedBeltAndRealSpecWeld.lean` and
`aeneas/lean/QsagVerified/Proofs/RealSpecGuardBoundary.lean`. Per model:

| Model here | Relationship to `aeneas/lean/QsagVerified/Types.lean` (`qsag_verified`) |
|---|---|
| `MirRssCutSession` / `mirRssCutMachine` (§3) | Exact 5-phase field layout of `rss_cut_session.RssCutGateSession` (`Types.lean:592-635`); linked in `qsag_aeneas` by `extractedRssCut_forwardSim_mirRssCut`. |
| `MirPolicyGuardState` (§2) & `MirStatefulVelocityGuard` (§6A) | `MirPolicyGuardState` is the `UInt64` burned-nonce model used in §5; the extracted guard does not refine it as a whole machine (`tooth_velocity_used_nonce_model_is_not_monotone_nonce`). `mirVelocityMachine` (§6A) is what `policy_and_addr.StatefulVelocityGuard::authorize_spend` computes (`velocity_extracted_step_refines`), and relates to `mirPolicyGuardMachine` on accepted steps (`mirVelocityAdapted_step_refines_mirPolicyGuard`). |
| `MirRssMlDsaKeyState` (§3) & `MirMlDsaReleaseGate` (§6B) | `MirRssMlDsaKeyState` computes FIPS 204 norms directly; `mirMlDsaReleaseMachine` (§6B) is what `cred_and_hd_guards.MlDsaReleaseGate::try_release_z_share` computes (`mlDsa_extracted_step_refines`). |
| `MirBeltLatchState` (§4), `MirBeltLatchKernel` & `MirBeltQuorumCore` (§6C) | `MirBeltLatchState` mirrors `WalLatchState`; `mirBeltLatchKernelMachine` (§6C) is what `belt_latch_kernel.BeltLatchKernel::bind` computes (`beltLatch_extracted_step_refines`). `MirBeltQuorumCore` / `mirValidateBeltQuorumConfig` have the field layout of `pants_and_quorum_guards.BeltQuorumCore` (`Types.lean:128-142`) and no extraction weld. |
| `Layer1ElfState`, `Layer2MirState` and the four-layer chain (§5) | Layer 1 runs decoded machine code through `McRefine`. Layer 2 evaluates the pre-cut transcript predicate directly and composes via `ForwardSim.trans` with generalized `ShamirThresholdSubset` reconstruction (`shamirSubset_four_layer_sim`). |

Names keep their `Mir` prefix because downstream modules refer to them; read it as
"model at MIR granularity", not "derived from MIR". The extraction welds named above live in
`aeneas/lean/QsagVerified/Proofs/RealSpecGuardBoundary.lean` and
`AuthenticatedBeltAndRealSpecWeld.lean`; each is a lockstep forward simulation from the extracted
step function to the machine here, so every trace theorem below about that machine also holds of
the extracted code.

## Contents

1. **§1. Compiled `.rlib` kernel bundle.** Packages the nine machine-code refinement theorems of
   `Qsag.McRefine` (`compiled_rlib_nine_kernels_verified`) over decoded x86-64 and AArch64 object
   slices, and restates `ct_eq_32`, `ct_memzero` and the Goldilocks kernels against digest
   equality, share wipe and `Goldilocks` ring arithmetic.

2. **§2. `UInt64` policy guard model.** `MirPolicyGuardState` with `LockstepSim` / `ForwardSim` to
   `CustodySuiteFull.policyGuardStep`, lifted to the multi-turn velocity and intent-binding
   theorem. The no-wrap invariant is an explicit premise.

3. **§3. Residual-gated cut session and ML-DSA gate model.**
   - `MirRssCutSession` mirrors `aeneas/qsag-verified/src/rss_cut_session.rs`: five phases,
     session-id and mask-commitment binding, and a Round-3 check that compares three
     caller-supplied residual scalars with zero. It evaluates no MAC relation.
   - `ResidualSound` / `ResidualContract` state the caller obligation that gives those scalars
     meaning. `guardedCut_released_cut_backed_by_witness` (multi-turn, composed with
     `HonestCustodyVault`) and `guardedCut_forwardSim_specPreCut` (forward simulation to a barrier
     spec that evaluates the relation) both take it as a hypothesis.
   - `mirRssCut_release_implies_barrier_and_deviation_root` instantiates the relation with the
     accumulator test of `RssSlhFullSecurity.sharedPreCutBarrier`
     (`sharedPreCutBarrier_pass_implies_preCutBarrierHolds` proves it is that test);
     `honestRound3Input_meets_contract` shows the contract is met by the honestly computed
     residual.
   - `mirRssMlDsaGate_forwardSim_spec` and the leakage characterisation for the ML-DSA model.

4. **§4. Quorum intersection and the belt latch model.** Constructive honest-intersection witness
   under `2 * q > n + f`; `mirBeltLatch_forwardSim_walLatch`, whose relation carries
   `WalLatchState.WellFormed`; an authenticated, deduplicated certificate gate
   (`beltCertAuthenticated`) with `beltCert_authenticated_quorums_share_honest_signer`.

5. **§5. Four-layer conditional refinement chain (`isa_to_mir_to_protocol_to_ideal_sim`) &
   generalized `ShamirThresholdSubset` reconstruction.**
   Conditional control-flow and authorization `ForwardSim.trans` across the decoded ELF slice,
   the Layer-2 guard model, the three-round interactive protocol, and the share-free Layer-4 guard
   state (parameterized at the cryptographic signing boundary by `hSigMatch` and `hOracleEq`),
   discharged for arbitrary distinct nonzero `t`-of-`n` threshold subsets via
   `shamirSubset_four_layer_sim`, paired with multi-subset completeness witnesses and sub-threshold
   ambiguity `#tooth` refutations.

6. **§6. Guard machines with the extracted carriers' field layout.**
   `StatefulVelocityGuard` (`u128` spend/cap, strictly increasing `u64` nonce), `MlDsaReleaseGate`
   (four-flag release barrier, share wiped on every refusal), `BeltLatchKernel` (capacity, jump
   window `≤ 64`, exact replay, poison) and `BeltQuorumCore` / `validate_belt_quorum_config`, each
   with its multi-turn trace invariant. The first three are welded to the extraction (above).

Constructive throughout: no proof gaps, no custom axioms, no `Classical.choice`.
-/

public section

namespace Qsag
attribute [-instance] Fin.instLinearOrderPackage
  Std.instLawfulEqOrdOfLawfulOrderOrdOfAntisymmLe
  Std.instLawfulEqOrdOfLawfulOrderOrdOfIsPartialOrder

attribute [-instance] UInt8.instLawfulEqOrd UInt64.instLawfulEqOrd BitVec.instLawfulEqOrd

set_option autoImplicit false
-- Bound diagnostics for examples containing fully instantiated cryptographic states.
set_option pp.maxSteps 1000
set_option maxRecDepth 8192

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

/-- Fixed-width model of a transaction intent request carrying `UInt64` numeric fields plus an
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

/-- Fixed-width `UInt64` policy guard model. It is not extracted from Rust and differs from both
    the extracted `StatefulVelocityGuard` (`u128`, monotonic nonce) and production
    `crates/qsag-policy` (`u128` caps, 32-byte nonces, authenticated peers). -/
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

/-! ## §3. Residual-gated cut session model, ML-DSA gate model, and their protocol bridges -/

/-- Concrete `BGIN19` `GF(2^128)` (`Tower128`) Round-2 wire-MAC relation check:
    `alpha * xWire + keyOffset = macShare` over `GF(2^128)` field elements. This is a
    protocol-level relation; no guard model in this file evaluates it on its own. -/
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

/-! ### Residual-gated `MirRssCutSession`

Hand-written fixed-width model of `RssCutGateSession` in
`aeneas/qsag-verified/src/rss_cut_session.rs`, kept field-for-field and branch-for-branch equal to
that Rust. This package does not import the Aeneas extraction, so nothing in this file relates the
model to MIR; that link is the forward simulation
`qsag_verified.proofs.extractedRssCut_forwardSim_mirRssCut` in
`aeneas/lean/QsagVerified/Proofs/AuthenticatedBeltAndRealSpecWeld.lean`, which imports both
`QsagVerified.Funs` and this module.

The guard evaluates no MAC and no zero-knowledge relation. Round 3 compares three caller-supplied
residual scalars with zero and nothing else. What those scalars summarise is an obligation on the
caller, stated below as `ResidualSound` / `ResidualContract`; every theorem here that speaks about
a protocol relation takes that obligation as an explicit hypothesis. The Rust error variants are
collapsed to `Unit`: every rejection poisons the session whatever its cause. -/

/-- Fixed-width 32-byte value: the model of a Rust `[u8; 32]`. -/
abbrev Bytes32 := Vector UInt8 32

/-- The wiped cut buffer `[0u8; 32]`. -/
def zeroBytes32 : Bytes32 := Vector.replicate 32 0

theorem zeroBytes32_eq : zeroBytes32 = Vector.replicate 32 0 := by rfl

/-- The five phases of `RssCutPhase`, in declaration order. -/
inductive MirRssCutPhase where
  | round1MaskCommitted
  | round2ChiEvaluated
  | round3ConsistencyVerified
  | cutOpened
  | poisoned
  deriving DecidableEq, Repr

/-- Model of the six private fields of `RssCutGateSession`. -/
structure MirRssCutSession where
  sessionId : Bytes32
  phase : MirRssCutPhase
  maskCommitment : Bytes32
  candidateCutBytes : Bytes32
  consistencyVerified : Bool
  poisoned : Bool
  deriving DecidableEq

/-- Model of `RssCutStepInput`. The Round-3 residuals are opaque scalars (`u128`, `u128`, `u64`)
    computed outside the guard. -/
inductive MirRssCutInput where
  | advanceRound2Chi (reqSessionId recomputedMaskCommitment chiCutCandidate : Bytes32)
  | advanceRound3VerifyConsistency (reqSessionId : Bytes32)
      (spdzMacResidualLo spdzMacResidualHi : BitVec 128) (bbcggiDzkResidual : UInt64)
  | openVerifiedCut (reqSessionId : Bytes32)
  deriving DecidableEq

/-- Model of `RssCutStepOutput`. -/
inductive MirRssCutOutput where
  | round2Ready
  | round3Verified
  | cutReleased (cut : Bytes32)
  deriving DecidableEq

/-- `RssCutGateSession::new_round1_committed`. -/
def MirRssCutSession.round1Committed (sessionId maskCommitment : Bytes32) : MirRssCutSession :=
  { sessionId := sessionId, phase := .round1MaskCommitted, maskCommitment := maskCommitment,
    candidateCutBytes := zeroBytes32, consistencyVerified := false, poisoned := false }

theorem MirRssCutSession.round1Committed_eq (sessionId maskCommitment : Bytes32) :
    MirRssCutSession.round1Committed sessionId maskCommitment =
      { sessionId := sessionId, phase := .round1MaskCommitted, maskCommitment := maskCommitment,
        candidateCutBytes := zeroBytes32, consistencyVerified := false, poisoned := false } := by rfl

/-- `poison_rss_cut_session`: sticky poison, wiped cut buffer, verification flag cleared. -/
def mirRssCutPoison (s : MirRssCutSession) : MirRssCutSession :=
  { sessionId := s.sessionId, phase := .poisoned, maskCommitment := s.maskCommitment,
    candidateCutBytes := zeroBytes32, consistencyVerified := false, poisoned := true }

theorem mirRssCutPoison_eq (s : MirRssCutSession) :
    mirRssCutPoison s =
      { sessionId := s.sessionId, phase := .poisoned, maskCommitment := s.maskCommitment,
        candidateCutBytes := zeroBytes32, consistencyVerified := false, poisoned := true } := by rfl

/-- The whole of the guard's Round-3 consistency check: three scalar comparisons with zero. -/
def residualsZero (lo hi : BitVec 128) (dzk : UInt64) : Bool :=
  decide (lo = 0) && decide (hi = 0) && decide (dzk = 0)

theorem residualsZero_eq (lo hi : BitVec 128) (dzk : UInt64) :
    residualsZero lo hi dzk = (decide (lo = 0) && decide (hi = 0) && decide (dzk = 0)) := by rfl

/-- Acceptance condition of each transition on an unpoisoned session. -/
def mirRssCutAccepts (s : MirRssCutSession) : MirRssCutInput → Bool
  | .advanceRound2Chi reqSid recomputed _ =>
    decide (s.sessionId = reqSid) && decide (s.phase = .round1MaskCommitted) &&
      decide (s.maskCommitment = recomputed)
  | .advanceRound3VerifyConsistency reqSid lo hi dzk =>
    decide (s.sessionId = reqSid) && decide (s.phase = .round2ChiEvaluated) &&
      residualsZero lo hi dzk
  | .openVerifiedCut reqSid =>
    decide (s.sessionId = reqSid) && decide (s.phase = .round3ConsistencyVerified) &&
      s.consistencyVerified

theorem mirRssCutAccepts_round2 (s : MirRssCutSession) (reqSid recomputed cand : Bytes32) :
    mirRssCutAccepts s (.advanceRound2Chi reqSid recomputed cand) =
      (decide (s.sessionId = reqSid) && decide (s.phase = .round1MaskCommitted) &&
        decide (s.maskCommitment = recomputed)) := by rfl

theorem mirRssCutAccepts_round3 (s : MirRssCutSession) (reqSid : Bytes32)
    (lo hi : BitVec 128) (dzk : UInt64) :
    mirRssCutAccepts s (.advanceRound3VerifyConsistency reqSid lo hi dzk) =
      (decide (s.sessionId = reqSid) && decide (s.phase = .round2ChiEvaluated) &&
        residualsZero lo hi dzk) := by rfl

theorem mirRssCutAccepts_open (s : MirRssCutSession) (reqSid : Bytes32) :
    mirRssCutAccepts s (.openVerifiedCut reqSid) =
      (decide (s.sessionId = reqSid) && decide (s.phase = .round3ConsistencyVerified) &&
        s.consistencyVerified) := by rfl

/-- Successor state and output of each accepted transition. -/
def mirRssCutNext (s : MirRssCutSession) : MirRssCutInput → MirRssCutSession × MirRssCutOutput
  | .advanceRound2Chi _ _ cand =>
    ({ s with phase := .round2ChiEvaluated, candidateCutBytes := cand,
              consistencyVerified := false }, .round2Ready)
  | .advanceRound3VerifyConsistency _ _ _ _ =>
    ({ s with phase := .round3ConsistencyVerified, consistencyVerified := true }, .round3Verified)
  | .openVerifiedCut _ =>
    ({ s with phase := .cutOpened, candidateCutBytes := zeroBytes32 },
      .cutReleased s.candidateCutBytes)

theorem mirRssCutNext_round2 (s : MirRssCutSession) (reqSid recomputed cand : Bytes32) :
    mirRssCutNext s (.advanceRound2Chi reqSid recomputed cand) =
      ({ s with phase := .round2ChiEvaluated, candidateCutBytes := cand,
                consistencyVerified := false }, .round2Ready) := by rfl

theorem mirRssCutNext_round3 (s : MirRssCutSession) (reqSid : Bytes32)
    (lo hi : BitVec 128) (dzk : UInt64) :
    mirRssCutNext s (.advanceRound3VerifyConsistency reqSid lo hi dzk) =
      ({ s with phase := .round3ConsistencyVerified, consistencyVerified := true },
        .round3Verified) := by rfl

theorem mirRssCutNext_open (s : MirRssCutSession) (reqSid : Bytes32) :
    mirRssCutNext s (.openVerifiedCut reqSid) =
      ({ s with phase := .cutOpened, candidateCutBytes := zeroBytes32 },
        .cutReleased s.candidateCutBytes) := by rfl

/-- The residual-gated cut session as a `PartyMachine`. Every rejection, whatever its cause,
    lands in `mirRssCutPoison`. -/
def mirRssCutMachine : PartyMachine MirRssCutSession MirRssCutInput MirRssCutOutput where
  step s inp :=
    if !s.poisoned && mirRssCutAccepts s inp then
      some ((mirRssCutNext s inp).1, (mirRssCutNext s inp).2)
    else none
  errStep s _ := mirRssCutPoison s

theorem mirRssCutMachine_step_eq (s : MirRssCutSession) (inp : MirRssCutInput) :
    mirRssCutMachine.step s inp =
      if !s.poisoned && mirRssCutAccepts s inp then
        some ((mirRssCutNext s inp).1, (mirRssCutNext s inp).2)
      else none := by rfl

theorem mirRssCutMachine_errStep_eq (s : MirRssCutSession) (inp : MirRssCutInput) :
    mirRssCutMachine.errStep s inp = mirRssCutPoison s := by rfl

/-- Mutant guard that returns to `round2ChiEvaluated` after a failed residual check instead of
    poisoning. -/
def nonStickyRssCutMachine : PartyMachine MirRssCutSession MirRssCutInput MirRssCutOutput where
  step s inp :=
    if !s.poisoned && mirRssCutAccepts s inp then
      some ((mirRssCutNext s inp).1, (mirRssCutNext s inp).2)
    else none
  errStep s _ := s

/-- **`#tooth` (`tooth_non_sticky_cut_session_releases_after_failed_residual`)**:
    after a Round-3 call with a non-zero residual, the non-sticky mutant accepts a retry with zero
    residuals and releases the candidate cut; the real guard has wiped the candidate, is poisoned,
    and rejects the same retry and the open. -/
theorem tooth_non_sticky_cut_session_releases_after_failed_residual
    (sid comm cand : Bytes32) :
    let init := MirRssCutSession.round1Committed sid comm
    let bad : MirRssCutInput := .advanceRound3VerifyConsistency sid 1 0 0
    let good : MirRssCutInput := .advanceRound3VerifyConsistency sid 0 0 0
    let m1 := (nonStickyRssCutMachine.runStep init (.advanceRound2Chi sid comm cand)).1
    let m2 := (nonStickyRssCutMachine.runStep m1 bad).1
    let m3 := (nonStickyRssCutMachine.runStep m2 good).1
    let g1 := (mirRssCutMachine.runStep init (.advanceRound2Chi sid comm cand)).1
    let g2 := (mirRssCutMachine.runStep g1 bad).1
    (nonStickyRssCutMachine.runStep m3 (.openVerifiedCut sid)).2 = some (.cutReleased cand) ∧
    g2.poisoned = true ∧
    g2.candidateCutBytes = zeroBytes32 ∧
    (mirRssCutMachine.runStep g2 good).2 = none ∧
    (mirRssCutMachine.runStep g2 (.openVerifiedCut sid)).2 = none := by
  simp [PartyMachine.runStep, nonStickyRssCutMachine, mirRssCutMachine, mirRssCutAccepts,
    mirRssCutNext, mirRssCutPoison, residualsZero, MirRssCutSession.round1Committed]

/-! ### Caller residual contract and the composed guard-plus-vault execution -/

/-- A guard input paired with the protocol-level witness the caller claims its Round-3 residual
    scalars summarise. The guard never reads `witness`. -/
structure AttestedCutInput (W : Type) where
  input : MirRssCutInput
  witness : W

/-- **Caller residual soundness.** If the residual scalars handed to Round 3 are all zero then the
    protocol relation `Holds` is true of the caller's witness. This is the only direction the
    release theorem needs, and it is an assumption about code outside the guard. -/
def ResidualSound {W : Type} (Holds : W → Bool) (a : AttestedCutInput W) : Prop :=
  ∀ reqSid lo hi dzk, a.input = .advanceRound3VerifyConsistency reqSid lo hi dzk →
    residualsZero lo hi dzk = true → Holds a.witness = true

/-- **Caller residual contract**: soundness and completeness together, i.e. the residuals are zero
    exactly when the relation holds. The forward simulation needs both directions because a spec
    that evaluates `Holds` must reject exactly when the guard does. -/
def ResidualContract {W : Type} (Holds : W → Bool) (a : AttestedCutInput W) : Prop :=
  ∀ reqSid lo hi dzk, a.input = .advanceRound3VerifyConsistency reqSid lo hi dzk →
    residualsZero lo hi dzk = Holds a.witness

theorem ResidualContract.sound {W : Type} {Holds : W → Bool} {a : AttestedCutInput W}
    (h : ResidualContract Holds a) : ResidualSound Holds a :=
  fun reqSid lo hi dzk hIn hZero => (h reqSid lo hi dzk hIn).symm.trans hZero

/-- Guard composed with the honest custody vault. The vault's share stays in memory only while the
    guard accepts; the released Round-3 cut is whatever the guard releases. -/
structure GuardedCutVaultState (ShareT : Type) where
  session : MirRssCutSession
  vault : HonestCustodyVault ShareT

/-- Quarantine of the composed state: poison the guard and erase the vault share. -/
def guardedCutPoison {ShareT : Type} (c : GuardedCutVaultState ShareT) :
    GuardedCutVaultState ShareT :=
  { session := mirRssCutPoison c.session, vault := walPoisonVault c.vault }

/-- The composed step is accepted when the vault is live and the guard accepts. -/
def guardedCutCond {ShareT : Type} (c : GuardedCutVaultState ShareT) (i : MirRssCutInput) : Bool :=
  !(c.vault.wal.poisoned || c.vault.shareSlot.isNone) &&
    (!c.session.poisoned && mirRssCutAccepts c.session i)

/-- **Composed execution.** Runs `mirRssCutMachine` on the session; any rejection quarantines the
    vault as well. The witness component of the input is ignored. -/
def guardedCutVaultMachine {W ShareT : Type} :
    PartyMachine (GuardedCutVaultState ShareT) (AttestedCutInput W) MirRssCutOutput where
  step c a :=
    if guardedCutCond c a.input then
      some ({ session := (mirRssCutNext c.session a.input).1, vault := c.vault },
            (mirRssCutNext c.session a.input).2)
    else none
  errStep c _ := guardedCutPoison c

/-- Every accepted composed step is an accepted step of the standalone guard with the same
    output, and leaves the vault untouched. -/
theorem guardedCutVaultMachine_ok_runs_guard {W ShareT : Type}
    {c c' : GuardedCutVaultState ShareT} {a : AttestedCutInput W} {out : MirRssCutOutput}
    (h : (guardedCutVaultMachine (W := W)).step c a = some (c', out)) :
    mirRssCutMachine.step c.session a.input = some (c'.session, out) ∧ c'.vault = c.vault := by
  dsimp only [guardedCutVaultMachine] at h
  cases hc : guardedCutCond c a.input
  · simp [hc] at h
  · simp only [hc, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    unfold guardedCutCond at hc
    simp only [Bool.and_eq_true] at hc
    refine ⟨?_, rfl⟩
    rw [mirRssCutMachine_step_eq, hc.2.1, hc.2.2]
    rfl

/-- Any rejected composed step erases the vault share, poisons the WAL and the guard, and wipes
    the candidate cut. -/
theorem guardedCutVaultMachine_reject_wipes {W ShareT : Type}
    (c : GuardedCutVaultState ShareT) (a : AttestedCutInput W) :
    let c' := (guardedCutVaultMachine (W := W)).errStep c a
    c'.vault.shareSlot = none ∧ c'.vault.wal.poisoned = true ∧
    c'.session.poisoned = true ∧ c'.session.candidateCutBytes = zeroBytes32 := by
  intro c'
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- A quarantined composed state accepts nothing. -/
theorem guardedCutVaultMachine_quarantined_rejects {W ShareT : Type}
    (c : GuardedCutVaultState ShareT) (a : AttestedCutInput W)
    (hQ : (c.vault.wal.poisoned || c.vault.shareSlot.isNone) = true) :
    (guardedCutVaultMachine (W := W)).step c a = none := by
  dsimp only [guardedCutVaultMachine]
  unfold guardedCutCond
  rw [hQ]
  rfl

/-- Trace predicate: each accepted Round 3 carries a witness for which `Holds` is true, and each
    released cut is backed by the most recent such witness with no Round 2 in between. -/
def CutReleasesBacked {W : Type} (Holds : W → Bool) :
    Option W → List (AttestedCutInput W × MirRssCutOutput) → Prop
  | _, [] => True
  | _, (_, .round2Ready) :: rest => CutReleasesBacked Holds none rest
  | _, (a, .round3Verified) :: rest =>
    Holds a.witness = true ∧ CutReleasesBacked Holds (some a.witness) rest
  | cur, (_, .cutReleased _) :: rest =>
    (∃ w, cur = some w ∧ Holds w = true) ∧ CutReleasesBacked Holds none rest

private theorem guardedCutCond_round3 {ShareT : Type} {c : GuardedCutVaultState ShareT}
    {reqSid : Bytes32} {lo hi : BitVec 128} {dzk : UInt64}
    (h : guardedCutCond c (.advanceRound3VerifyConsistency reqSid lo hi dzk) = true) :
    residualsZero lo hi dzk = true := by
  unfold guardedCutCond at h
  rw [mirRssCutAccepts_round3] at h
  simp only [Bool.and_eq_true] at h
  exact h.2.2.2

private theorem guardedCutCond_open {ShareT : Type} {c : GuardedCutVaultState ShareT}
    {reqSid : Bytes32} (h : guardedCutCond c (.openVerifiedCut reqSid) = true) :
    c.session.phase = .round3ConsistencyVerified := by
  unfold guardedCutCond at h
  rw [mirRssCutAccepts_open] at h
  simp only [Bool.and_eq_true] at h
  exact of_decide_eq_true h.2.2.1.2

/-- Generalised induction behind `guardedCut_released_cut_backed_by_witness`. -/
private theorem guardedCut_trace_backed {W ShareT : Type} (Holds : W → Bool) :
    ∀ {c c_f : GuardedCutVaultState ShareT}
      {tr : List (AttestedCutInput W × MirRssCutOutput)} {cur : Option W},
      (guardedCutVaultMachine (W := W)).ValidTrace c tr c_f →
      (∀ p ∈ tr, ResidualSound Holds p.1) →
      (c.session.phase = .round3ConsistencyVerified → ∃ w, cur = some w ∧ Holds w = true) →
      CutReleasesBacked Holds cur tr := by
  intro c c_f tr cur hTr
  induction hTr generalizing cur with
  | nil _ => intro _ _; trivial
  | @accept s s' s_f inp out rest hStep _ ih =>
    intro hSound hInv
    have hSoundRest : ∀ p ∈ rest, ResidualSound Holds p.1 :=
      fun p hp => hSound p (List.mem_cons_of_mem _ hp)
    have hSoundHead : ResidualSound Holds inp := hSound (inp, out) List.mem_cons_self
    dsimp only [guardedCutVaultMachine] at hStep
    cases hc : guardedCutCond s inp.input
    · simp [hc] at hStep
    · simp only [hc, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hStep
      obtain ⟨hS', hOut⟩ := hStep
      subst hS'
      subst hOut
      cases hIn : inp.input with
      | advanceRound2Chi reqSid recomputed cand =>
        show CutReleasesBacked Holds none rest
        exact ih hSoundRest (fun h => by
          rw [hIn] at h
          exact absurd (show MirRssCutPhase.round2ChiEvaluated =
            MirRssCutPhase.round3ConsistencyVerified from h) (by decide))
      | advanceRound3VerifyConsistency reqSid lo hi dzk =>
        rw [hIn] at hc
        have hHolds : Holds inp.witness = true :=
          hSoundHead reqSid lo hi dzk hIn (guardedCutCond_round3 hc)
        show Holds inp.witness = true ∧ CutReleasesBacked Holds (some inp.witness) rest
        exact ⟨hHolds, ih hSoundRest (fun _ => ⟨inp.witness, rfl, hHolds⟩)⟩
      | openVerifiedCut reqSid =>
        rw [hIn] at hc
        show (∃ w, cur = some w ∧ Holds w = true) ∧ CutReleasesBacked Holds none rest
        exact ⟨hInv (guardedCutCond_open hc),
          ih hSoundRest (fun h => by
            rw [hIn] at h
            exact absurd (show MirRssCutPhase.cutOpened =
            MirRssCutPhase.round3ConsistencyVerified from h) (by decide))⟩
  | @reject s s_f inp rest _ _ ih =>
    intro hSound _
    exact ih hSound (fun h => absurd (show MirRssCutPhase.poisoned =
            MirRssCutPhase.round3ConsistencyVerified from h) (by decide))

/-- **Release theorem (`guardedCut_released_cut_backed_by_witness`).**
    Start the composed guard-plus-vault execution in Round 1. Along any multi-turn trace whose
    accepted Round-3 inputs satisfy the caller obligation `ResidualSound Holds`, every accepted
    Round 3 has a witness for which `Holds` is true, and every released cut is backed by the most
    recent such witness. Without the hypothesis the guard guarantees only that three scalars were
    zero. -/
theorem guardedCut_released_cut_backed_by_witness {W ShareT : Type} (Holds : W → Bool)
    (sessionId maskCommitment : Bytes32) (vault : HonestCustodyVault ShareT)
    {c_f : GuardedCutVaultState ShareT}
    {trace : List (AttestedCutInput W × MirRssCutOutput)}
    (hTrace : (guardedCutVaultMachine (W := W)).ValidTrace
      { session := MirRssCutSession.round1Committed sessionId maskCommitment, vault := vault }
      trace c_f)
    (hResidual : ∀ p ∈ trace, ResidualSound Holds p.1) :
    CutReleasesBacked Holds none trace :=
  guardedCut_trace_backed Holds hTrace hResidual (fun h =>
    absurd (show MirRssCutPhase.round1MaskCommitted =
            MirRssCutPhase.round3ConsistencyVerified from h) (by decide))

/-- Corollary for `BGIN19` wire-MAC batches: under the caller obligation
    `residualsZero lo hi dzk = true → bginBatchHolds relations = true`, every released cut is
    backed by a batch all of whose `GF(2^128)` relations hold. -/
theorem mirRssCut_released_cut_backed_by_bginBatch {ShareT : Type}
    (sessionId maskCommitment : Bytes32) (vault : HonestCustodyVault ShareT)
    {c_f : GuardedCutVaultState ShareT}
    {trace : List (AttestedCutInput (List BginWireRelation) × MirRssCutOutput)}
    (hTrace : (guardedCutVaultMachine (W := List BginWireRelation)).ValidTrace
      { session := MirRssCutSession.round1Committed sessionId maskCommitment, vault := vault }
      trace c_f)
    (hResidual : ∀ p ∈ trace, ResidualSound bginBatchHolds p.1) :
    CutReleasesBacked bginBatchHolds none trace :=
  guardedCut_released_cut_backed_by_witness bginBatchHolds sessionId maskCommitment vault
    hTrace hResidual

/-! ### Protocol-level pre-cut barrier specification and the forward simulation -/

/-- Protocol-level pre-cut barrier state over an `HonestCustodyVault`. It has no residual scalars
    and no verification flag: Round 3 evaluates the relation `Holds` on the witness itself. -/
structure SpecPreCutVaultState (ShareT : Type) where
  sessionId : Bytes32
  maskCommitment : Bytes32
  stage : MirRssCutPhase
  candidate : Bytes32
  vault : HonestCustodyVault ShareT

def specPreCutPoison {ShareT : Type} (st : SpecPreCutVaultState ShareT) :
    SpecPreCutVaultState ShareT :=
  { st with stage := .poisoned, candidate := zeroBytes32, vault := walPoisonVault st.vault }

def specPreCutAccepts {W ShareT : Type} (Holds : W → Bool) (st : SpecPreCutVaultState ShareT)
    (w : W) : MirRssCutInput → Bool
  | .advanceRound2Chi reqSid recomputed _ =>
    decide (st.sessionId = reqSid) && decide (st.stage = .round1MaskCommitted) &&
      decide (st.maskCommitment = recomputed)
  | .advanceRound3VerifyConsistency reqSid _ _ _ =>
    decide (st.sessionId = reqSid) && decide (st.stage = .round2ChiEvaluated) && Holds w
  | .openVerifiedCut reqSid =>
    decide (st.sessionId = reqSid) && decide (st.stage = .round3ConsistencyVerified)

def specPreCutNext {ShareT : Type} (st : SpecPreCutVaultState ShareT) :
    MirRssCutInput → SpecPreCutVaultState ShareT × MirRssCutOutput
  | .advanceRound2Chi _ _ cand =>
    ({ st with stage := .round2ChiEvaluated, candidate := cand }, .round2Ready)
  | .advanceRound3VerifyConsistency _ _ _ _ =>
    ({ st with stage := .round3ConsistencyVerified }, .round3Verified)
  | .openVerifiedCut _ =>
    ({ st with stage := .cutOpened, candidate := zeroBytes32 }, .cutReleased st.candidate)

def specPreCutCond {W ShareT : Type} (Holds : W → Bool) (st : SpecPreCutVaultState ShareT)
    (a : AttestedCutInput W) : Bool :=
  !(st.vault.wal.poisoned || st.vault.shareSlot.isNone) &&
    specPreCutAccepts Holds st a.witness a.input

/-- Protocol-level pre-cut barrier machine. -/
def specPreCutVaultMachine {W ShareT : Type} (Holds : W → Bool) :
    PartyMachine (SpecPreCutVaultState ShareT) (AttestedCutInput W) MirRssCutOutput where
  step st a :=
    if specPreCutCond Holds st a then
      some ((specPreCutNext st a.input).1, (specPreCutNext st a.input).2)
    else none
  errStep st _ := specPreCutPoison st

/-- Restrict a machine to a subtype of its inputs. -/
def PartyMachine.restrictInputs {S In Out : Type} (M : PartyMachine S In Out) (P : In → Prop) :
    PartyMachine S { i : In // P i } Out where
  step s i := M.step s i.1
  errStep s i := M.errStep s i.1

/-- Simulation relation between the composed guard-plus-vault state and the barrier spec. -/
def CutVaultRel {ShareT : Type} (c : GuardedCutVaultState ShareT)
    (a : SpecPreCutVaultState ShareT) : Prop :=
  a.vault = c.vault ∧ a.sessionId = c.session.sessionId ∧
  a.maskCommitment = c.session.maskCommitment ∧
  ((c.vault.wal.poisoned || c.vault.shareSlot.isNone) = false →
    c.session.poisoned = false ∧ a.stage = c.session.phase ∧
    a.candidate = c.session.candidateCutBytes ∧
    (c.session.phase = .round3ConsistencyVerified → c.session.consistencyVerified = true))

private theorem cutVault_cond_agree {W ShareT : Type} (Holds : W → Bool)
    {c : GuardedCutVaultState ShareT} {a : SpecPreCutVaultState ShareT}
    (inp : AttestedCutInput W) (hC : ResidualContract Holds inp) (hRel : CutVaultRel c a) :
    specPreCutCond Holds a inp = guardedCutCond c inp.input := by
  obtain ⟨hVault, hSid, hComm, hClean⟩ := hRel
  unfold specPreCutCond guardedCutCond
  rw [hVault]
  cases hQ : (c.vault.wal.poisoned || c.vault.shareSlot.isNone)
  · obtain ⟨hPois, hStage, _, hCv⟩ := hClean hQ
    rw [hPois]
    show specPreCutAccepts Holds a inp.witness inp.input = mirRssCutAccepts c.session inp.input
    cases hIn : inp.input with
    | advanceRound2Chi reqSid recomputed cand =>
      show (decide (a.sessionId = reqSid) && decide (a.stage = .round1MaskCommitted) &&
        decide (a.maskCommitment = recomputed)) = _
      rw [hSid, hComm, hStage]
      rfl
    | advanceRound3VerifyConsistency reqSid lo hi dzk =>
      show (decide (a.sessionId = reqSid) && decide (a.stage = .round2ChiEvaluated) &&
        Holds inp.witness) = _
      rw [hSid, hStage, ← hC reqSid lo hi dzk hIn]
      rfl
    | openVerifiedCut reqSid =>
      show (decide (a.sessionId = reqSid) && decide (a.stage = .round3ConsistencyVerified)) =
        (decide (c.session.sessionId = reqSid) &&
          decide (c.session.phase = .round3ConsistencyVerified) && c.session.consistencyVerified)
      rw [hSid, hStage]
      cases hPh : decide (c.session.phase = .round3ConsistencyVerified)
      · simp only [Bool.and_false, Bool.false_and]
      · rw [hCv (of_decide_eq_true hPh)]
        simp only [Bool.and_true]
  · rfl

private theorem cutVault_next_rel {ShareT : Type}
    {c : GuardedCutVaultState ShareT} {a : SpecPreCutVaultState ShareT}
    (i : MirRssCutInput) (hRel : CutVaultRel c a)
    (hQ : (c.vault.wal.poisoned || c.vault.shareSlot.isNone) = false) :
    (specPreCutNext a i).2 = (mirRssCutNext c.session i).2 ∧
    CutVaultRel { session := (mirRssCutNext c.session i).1, vault := c.vault }
      (specPreCutNext a i).1 := by
  obtain ⟨hVault, hSid, hComm, hClean⟩ := hRel
  obtain ⟨hPois, hStage, hCand, _⟩ := hClean hQ
  cases i with
  | advanceRound2Chi reqSid recomputed cand =>
    exact ⟨rfl, hVault, hSid, hComm, fun _ => ⟨hPois, rfl, rfl, fun h =>
      absurd (show MirRssCutPhase.round2ChiEvaluated =
            MirRssCutPhase.round3ConsistencyVerified from h) (by decide)⟩⟩
  | advanceRound3VerifyConsistency reqSid lo hi dzk =>
    exact ⟨rfl, hVault, hSid, hComm, fun _ => ⟨hPois, rfl, hCand, fun _ => rfl⟩⟩
  | openVerifiedCut reqSid =>
    exact ⟨congrArg MirRssCutOutput.cutReleased hCand, hVault, hSid, hComm,
      fun _ => ⟨hPois, rfl, rfl, fun h =>
        absurd (show MirRssCutPhase.cutOpened =
            MirRssCutPhase.round3ConsistencyVerified from h) (by decide)⟩⟩

private theorem cutVault_poison_rel {ShareT : Type}
    {c : GuardedCutVaultState ShareT} {a : SpecPreCutVaultState ShareT}
    (hRel : CutVaultRel c a) : CutVaultRel (guardedCutPoison c) (specPreCutPoison a) := by
  obtain ⟨hVault, hSid, hComm, _⟩ := hRel
  refine ⟨congrArg walPoisonVault hVault, hSid, hComm, fun h => ?_⟩
  exact absurd (show true = false from h) (by decide)

/-- **Bridge 3A (`guardedCut_forwardSim_specPreCut`).**
    On inputs that satisfy `ResidualContract Holds`, the composed residual-gated guard-plus-vault
    execution forward-simulates the protocol-level barrier that evaluates `Holds` directly:
    identical outputs, identical accept/reject decisions, and quarantine (vault share erased, WAL
    poisoned) in lockstep. The contract is carried by the input type; nothing is proved for inputs
    outside it. -/
def guardedCut_forwardSim_specPreCut {W ShareT : Type} (Holds : W → Bool) :
    ForwardSim
      ((guardedCutVaultMachine (W := W) (ShareT := ShareT)).restrictInputs (ResidualContract Holds))
      ((specPreCutVaultMachine (ShareT := ShareT) Holds).restrictInputs (ResidualContract Holds)) where
  Rel := CutVaultRel
  sim_ok {c c' a inp out} hRel hStepC := by
    have hAgree := cutVault_cond_agree Holds inp.1 inp.2 hRel
    dsimp only [PartyMachine.restrictInputs, guardedCutVaultMachine, specPreCutVaultMachine]
      at hStepC ⊢
    rw [hAgree]
    cases hc : guardedCutCond c inp.1.input
    · simp [hc] at hStepC
    · simp only [hc, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hStepC
      obtain ⟨hC', hOut⟩ := hStepC
      subst hC'
      subst hOut
      have hQ : (c.vault.wal.poisoned || c.vault.shareSlot.isNone) = false := by
        unfold guardedCutCond at hc
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
        exact hc.1
      exact cutVault_next_rel inp.1.input hRel hQ
  sim_err {c a inp} hRel hNoneC := by
    have hAgree := cutVault_cond_agree Holds inp.1 inp.2 hRel
    dsimp only [PartyMachine.restrictInputs, guardedCutVaultMachine, specPreCutVaultMachine]
      at hNoneC ⊢
    rw [hAgree]
    cases hc : guardedCutCond c inp.1.input
    · exact ⟨rfl, cutVault_poison_rel hRel⟩
    · simp [hc] at hNoneC

/-- The Round-1 composed state and the Round-1 barrier spec state are related. -/
theorem cutVaultRel_round1 {ShareT : Type} (sessionId maskCommitment : Bytes32)
    (vault : HonestCustodyVault ShareT) :
    CutVaultRel
      { session := MirRssCutSession.round1Committed sessionId maskCommitment, vault := vault }
      { sessionId := sessionId, maskCommitment := maskCommitment, stage := .round1MaskCommitted,
        candidate := zeroBytes32, vault := vault } :=
  ⟨rfl, rfl, rfl, fun _ => ⟨rfl, rfl, rfl, fun h =>
    absurd (show MirRssCutPhase.round1MaskCommitted =
            MirRssCutPhase.round3ConsistencyVerified from h) (by decide)⟩⟩

/-! ### Instance: the `BBCGGI19` accumulator check of `sharedPreCutBarrier` -/

/-- The wires and challenge of one pre-cut consistency check. -/
structure RssCutRound3Witness where
  sentWires : List Tower128
  expectedWires : List Tower128
  gamma : Tower128

/-- The algebraic acceptance test that `RssSlhFullSecurity.sharedPreCutBarrier` applies before
    Round 3: equality of the two `GF(2^128)` Horner accumulators at the challenge. -/
def preCutBarrierHolds (w : RssCutRound3Witness) : Bool :=
  bbcggiWireAccumulator w.sentWires w.gamma == bbcggiWireAccumulator w.expectedWires w.gamma

/-- Residual an honest caller derives from the witness: the packed 128-bit difference of the two
    accumulators in the low lane, zero in the other two. -/
def honestRound3Input (reqSid : Bytes32) (w : RssCutRound3Witness) :
    AttestedCutInput RssCutRound3Witness :=
  { input := .advanceRound3VerifyConsistency reqSid
      (packTower 7 (towerAdd 7 (bbcggiWireAccumulator w.sentWires w.gamma)
        (bbcggiWireAccumulator w.expectedWires w.gamma))) 0 0
    witness := w }

/-- The contract is satisfiable and deterministic: the honestly computed residual is zero exactly
    when the accumulators agree. -/
theorem honestRound3Input_meets_contract (reqSid : Bytes32) (w : RssCutRound3Witness) :
    ResidualContract preCutBarrierHolds (honestRound3Input reqSid w) := by
  intro reqSid' lo hi dzk hIn
  have hIn' : MirRssCutInput.advanceRound3VerifyConsistency reqSid
      (packTower 7 (towerAdd 7 (bbcggiWireAccumulator w.sentWires w.gamma)
        (bbcggiWireAccumulator w.expectedWires w.gamma))) 0 0 =
      MirRssCutInput.advanceRound3VerifyConsistency reqSid' lo hi dzk := hIn
  injection hIn' with _ hLo hHi hDzk
  subst hLo
  subst hHi
  subst hDzk
  show residualsZero _ 0 0 = (bbcggiWireAccumulator w.sentWires w.gamma ==
    bbcggiWireAccumulator w.expectedWires w.gamma)
  unfold residualsZero
  simp only [decide_true, Bool.and_true]
  by_cases hEq : bbcggiWireAccumulator w.sentWires w.gamma =
      bbcggiWireAccumulator w.expectedWires w.gamma
  · rw [hEq, towerAdd_self_zero, packTower_zero, beq_self_eq_true]
    exact decide_eq_true rfl
  · rw [beq_false_of_ne hEq]
    refine decide_eq_false (fun hZero => hEq ?_)
    have hAdd : towerAdd 7 (bbcggiWireAccumulator w.sentWires w.gamma)
        (bbcggiWireAccumulator w.expectedWires w.gamma) = towerZero 7 :=
      packTower_injective 7 _ _ (hZero.trans (packTower_zero 7).symm)
    have hCancel := congrArg (towerAdd 7 (bbcggiWireAccumulator w.sentWires w.gamma)) hAdd
    rw [towerAdd_cancel, towerAdd_zero] at hCancel
    exact hCancel.symm

/-- `preCutBarrierHolds` is the test the protocol applies, by proof rather than by reading:
    whenever `RssSlhFullSecurity.sharedPreCutBarrier` lets a session proceed to Round 3, the wires
    it hands on and the session challenge `unpackTower 7 r2St.gammaBits` pass
    `preCutBarrierHolds`. -/
theorem sharedPreCutBarrier_pass_implies_preCutBarrierHolds (cIdx : Fin 3) (deg : Nat)
    (pk : SlhPublicKey) (req : SessionScheduleReq) (r2St : RssRound2State)
    (corrR2 : List (Nat × ByteArray)) (r3Init : RssRound3State)
    (hBar : sharedPreCutBarrier cIdx deg pk req r2St corrR2 = .inr r3Init) :
    preCutBarrierHolds
      ⟨r3Init.sentWires, r3Init.expectedWires, unpackTower 7 r2St.gammaBits⟩ = true := by
  obtain ⟨_, hBatch, hLen⟩ :=
    sharedPreCutBarrier_extract_eq cIdx deg pk req r2St corrR2 r3Init hBar
  show (bbcggiWireAccumulator r3Init.sentWires (unpackTower 7 r2St.gammaBits) ==
    bbcggiWireAccumulator r3Init.expectedWires (unpackTower 7 r2St.gammaBits)) = true
  rw [bbcggiWireAccumulator_eq_iff_batchDeviationPoly hLen]
  exact hBatch

/-- **Bridge 3B (`mirRssCut_release_implies_barrier_and_deviation_root`).**
    Composed bad-event statement for the accumulator instance. Along any trace of the composed
    guard-plus-vault execution whose accepted Round-3 inputs satisfy the caller obligation for
    `preCutBarrierHolds`:
    1. every released cut is backed by a witness that passes the accumulator test of
       `sharedPreCutBarrier`;
    2. for any such witness with equal wire counts, the challenge is a root of the batch deviation
       polynomial of `sentWires ⊕ expectedWires`. So a cut released over inconsistent wires puts
       `gamma` among the roots of a non-zero polynomial, which is the event bounded by
       `RssSlhFullSecurity.activeConsistencyBreak_implies_schwartzZippel_root`.
    This theorem does not mention `EUF-CMA` or the `UC` game; it is the gate those arguments
    assume. -/
theorem mirRssCut_release_implies_barrier_and_deviation_root {ShareT : Type}
    (sessionId maskCommitment : Bytes32) (vault : HonestCustodyVault ShareT)
    {c_f : GuardedCutVaultState ShareT}
    {trace : List (AttestedCutInput RssCutRound3Witness × MirRssCutOutput)}
    (hTrace : (guardedCutVaultMachine (W := RssCutRound3Witness)).ValidTrace
      { session := MirRssCutSession.round1Committed sessionId maskCommitment, vault := vault }
      trace c_f)
    (hResidual : ∀ p ∈ trace, ResidualSound preCutBarrierHolds p.1) :
    CutReleasesBacked preCutBarrierHolds none trace ∧
    (∀ w : RssCutRound3Witness, preCutBarrierHolds w = true →
      w.sentWires.length = w.expectedWires.length →
      (batchDeviationPoly (zipXorTower 7 w.sentWires w.expectedWires) w.gamma ==
        towerZero 7) = true) :=
  ⟨guardedCut_released_cut_backed_by_witness preCutBarrierHolds sessionId maskCommitment vault
      hTrace hResidual,
    fun w hHolds hLen =>
      (bbcggiWireAccumulator_eq_iff_batchDeviationPoly hLen w.gamma).symm.trans hHolds⟩

/-- Non-vacuity of the release theorem: an honest three-step run (Round 2, honest Round 3 over
    agreeing wires, open) is a valid composed trace that releases the candidate cut, and its
    Round-3 input meets the contract. -/
theorem inhabited_guardedCut_honest_release {ShareT : Type}
    (sid comm cand : Bytes32) (vault : HonestCustodyVault ShareT)
    (hPois : vault.wal.poisoned = false) (hShare : vault.shareSlot ≠ none)
    (wires : List Tower128) (gamma : Tower128) :
    let w : RssCutRound3Witness := ⟨wires, wires, gamma⟩
    let r2 : AttestedCutInput RssCutRound3Witness := ⟨.advanceRound2Chi sid comm cand, w⟩
    let r3 := honestRound3Input sid w
    let op : AttestedCutInput RssCutRound3Witness := ⟨.openVerifiedCut sid, w⟩
    ResidualContract preCutBarrierHolds r3 ∧
    ∃ c_f, (guardedCutVaultMachine (W := RssCutRound3Witness)).ValidTrace
      { session := MirRssCutSession.round1Committed sid comm, vault := vault }
      [(r2, .round2Ready), (r3, .round3Verified), (op, .cutReleased cand)] c_f := by
  intro w r2 r3 op
  refine ⟨honestRound3Input_meets_contract sid w, ?_⟩
  let s1 : MirRssCutSession :=
    { sessionId := sid, phase := .round2ChiEvaluated, maskCommitment := comm,
      candidateCutBytes := cand, consistencyVerified := false, poisoned := false }
  let s2 : MirRssCutSession :=
    { sessionId := sid, phase := .round3ConsistencyVerified, maskCommitment := comm,
      candidateCutBytes := cand, consistencyVerified := true, poisoned := false }
  let s3 : MirRssCutSession :=
    { sessionId := sid, phase := .cutOpened, maskCommitment := comm,
      candidateCutBytes := zeroBytes32, consistencyVerified := true, poisoned := false }
  have h1 : (guardedCutVaultMachine (W := RssCutRound3Witness)).step
      ⟨MirRssCutSession.round1Committed sid comm, vault⟩ r2 =
      some (⟨s1, vault⟩, .round2Ready) := by
    simp [guardedCutVaultMachine, guardedCutCond, hPois, hShare, mirRssCutAccepts, mirRssCutNext,
      MirRssCutSession.round1Committed, r2, s1]
  have h2 : (guardedCutVaultMachine (W := RssCutRound3Witness)).step ⟨s1, vault⟩ r3 =
      some (⟨s2, vault⟩, .round3Verified) := by
    simp [guardedCutVaultMachine, guardedCutCond, hPois, hShare, mirRssCutAccepts, mirRssCutNext,
      honestRound3Input, residualsZero, r3, w, s1, s2, towerAdd_self_zero, packTower_zero]
  have h3 : (guardedCutVaultMachine (W := RssCutRound3Witness)).step ⟨s2, vault⟩ op =
      some (⟨s3, vault⟩, .cutReleased cand) := by
    simp [guardedCutVaultMachine, guardedCutCond, hPois, hShare, mirRssCutAccepts, mirRssCutNext,
      op, s2, s3]
  exact ⟨_, .accept h1 (.accept h2 (.accept h3 (.nil _)))⟩

/-! ### Fixed-Width `UInt64` Norm/Hint Rejection Gate $\to$ `ThresholdMlDsaAndToprf` Bridge -/

private theorem fq204_centeredAbs_lt_u64 (x : Fq204) :
    Fq204.centeredAbs x < 18446744073709551616 := by
  unfold Fq204.centeredAbs
  have hx : x.val < mldsaQ := x.isLt
  have hQ : mldsaQ = 8380417 := rfl
  split <;> omega

private theorem polyTree_infNorm_lt_u64 : ∀ {d : Nat} (p : PolyTree d),
    PolyTree.infNorm p < 18446744073709551616
  | 0, .leaf x => fq204_centeredAbs_lt_u64 x
  | _ + 1, .branch a b => by
    simp only [PolyTree.infNorm]
    have ha := polyTree_infNorm_lt_u64 a
    have hb := polyTree_infNorm_lt_u64 b
    omega

private theorem infNormVec4_lt_u64 (v : PolyVec4) :
    infNormVec4 v < 18446744073709551616 := by
  unfold infNormVec4
  have h0 := polyTree_infNorm_lt_u64 (v ⟨0, by decide⟩)
  have h1 := polyTree_infNorm_lt_u64 (v ⟨1, by decide⟩)
  have h2 := polyTree_infNorm_lt_u64 (v ⟨2, by decide⟩)
  have h3 := polyTree_infNorm_lt_u64 (v ⟨3, by decide⟩)
  omega

private theorem centeredDiffNormTree_lt_u64 :
    ∀ {d : Nat} (r : PolyTree d) (w1 : NatTree d),
      centeredDiffNormTree r w1 < 18446744073709551616
  | 0, .leaf r, .leaf w1 => fq204_centeredAbs_lt_u64 _
  | _ + 1, .branch r0 r1, .branch w0 w1 => by
    simp only [centeredDiffNormTree]
    have h0 := centeredDiffNormTree_lt_u64 r0 w0
    have h1 := centeredDiffNormTree_lt_u64 r1 w1
    omega

private theorem centeredDiffNormVec4_lt_u64 (r : PolyVec4) (w1 : Fin 4 → NatTree 8) :
    centeredDiffNormVec4 r w1 < 18446744073709551616 := by
  unfold centeredDiffNormVec4
  have h0 := centeredDiffNormTree_lt_u64 (r ⟨0, by decide⟩) (w1 ⟨0, by decide⟩)
  have h1 := centeredDiffNormTree_lt_u64 (r ⟨1, by decide⟩) (w1 ⟨1, by decide⟩)
  have h2 := centeredDiffNormTree_lt_u64 (r ⟨2, by decide⟩) (w1 ⟨2, by decide⟩)
  have h3 := centeredDiffNormTree_lt_u64 (r ⟨3, by decide⟩) (w1 ⟨3, by decide⟩)
  omega

private theorem hintWeightTree_le_pow : ∀ {d : Nat} (h : HintTree d),
    HintTree.weight h ≤ 2 ^ d
  | 0, .leaf b => by
    simp only [HintTree.weight]
    cases b <;> decide
  | d + 1, .branch h0 h1 => by
    simp only [HintTree.weight]
    have ih0 := hintWeightTree_le_pow h0
    have ih1 := hintWeightTree_le_pow h1
    rw [Nat.pow_succ]
    omega

private theorem hintWeightVec4_lt_u64 (h : Fin 4 → HintTree 8) :
    hintWeightVec4 h < 18446744073709551616 := by
  unfold hintWeightVec4
  have h0 := hintWeightTree_le_pow (h ⟨0, by decide⟩)
  have h1 := hintWeightTree_le_pow (h ⟨1, by decide⟩)
  have h2 := hintWeightTree_le_pow (h ⟨2, by decide⟩)
  have h3 := hintWeightTree_le_pow (h ⟨3, by decide⟩)
  have h256 : (2 : Nat) ^ 8 = 256 := rfl
  omega

/-- Zero vector in $R_q^4$ for summing RSS subset polynomial shares (`threshold_mldsa.rs:826-827`). -/
def zeroPolyVec4 : PolyVec4 := fun _ => PolyTree.zero 8

/-- Reconstructs a logical $R_q^4$ vector from RSS subset components (`s1_hat`, `s2_hat`, `y.c`). -/
def sumPolyVec4List : List PolyVec4 → PolyVec4
  | [] => zeroPolyVec4
  | v :: vs => addVec4 v (sumPolyVec4List vs)

/-- Constructive `SimpleEquiv` bijection (`0 Classical.choice`) proving that adding a uniform
    Phase-1/Phase-3 conversion mask (`wMask`, `zMask`, `lowMask` in `threshold_mldsa.rs:790, 981`)
    maps $R_q^4$ bijectively onto $R_q^4$ for every fixed unmasked vector `v`. -/
def rssMaskVec4Equiv (v : PolyVec4) : SimpleEquiv PolyVec4 PolyVec4 where
  toFun mask := addVec4 v mask
  invFun opened := subVec4 opened v
  left_inv mask := by
    funext i
    dsimp only [subVec4, addVec4]
    rw [polyTree_sub_eq_add_neg, polyTree_add_comm, ← polyTree_add_assoc,
        polyTree_add_left_neg, polyTree_zero_add]
  right_inv opened := by
    funext i
    dsimp only [subVec4, addVec4]
    rw [polyTree_sub_eq_add_neg, polyTree_add_comm (opened i) (PolyTree.neg (v i)),
        ← polyTree_add_assoc, polyTree_add_comm (v i) (PolyTree.neg (v i)),
        polyTree_add_left_neg, polyTree_zero_add]

/-- Concrete fixed-width `UInt64`-epoch RSS threshold ML-DSA session state (`threshold_mldsa.rs:801, 945`):
    stores RSS subset polynomial components `s1Hat`, `s2Hat` rather than an unshared key. -/
structure MirRssMlDsaKeyState where
  nextEpoch : UInt64
  A : PolyMat4
  s1Hat : List PolyVec4
  s2Hat : List PolyVec4

/-- Specification RSS threshold ML-DSA session state with unbounded `Nat` epoch counter. -/
structure SpecRssMlDsaKeyState where
  nextEpoch : Nat
  A : PolyMat4
  s1Hat : List PolyVec4
  s2Hat : List PolyVec4

def MirRssMlDsaKeyState.toSpec (st : MirRssMlDsaKeyState) : SpecRssMlDsaKeyState where
  nextEpoch := st.nextEpoch.toNat
  A := st.A
  s1Hat := st.s1Hat
  s2Hat := st.s2Hat

/-- Per-attempt RSS threshold ML-DSA signing input (`threshold_mldsa.rs:944-1038`) carrying RSS
    mask shares `yShares` and Phase-1/Phase-3 conversion masks `wMask`, `zMask`, `lowMask`. -/
structure MirRssMlDsaAttempt where
  epoch : UInt64
  mu : List UInt8
  yShares : List PolyVec4
  wMask : PolyVec4
  zMask : PolyVec4
  lowMask : PolyVec4

/-- Explicit transcript leakage opened during an RSS ML-DSA attempt (`threshold_mldsa.rs:58-62,
    790-798, 981, 987, 1001, 1036`): rejected attempts genuinely reveal `openedMaskedW`, public
    `openedW1 = HighBits(w)`, optional Phase-3 `openedMaskedZAndLow`, and `rejectBit`. -/
structure MirMlDsaAttemptLeakage where
  openedMaskedW : PolyVec4
  openedW1 : Fin 4 → NatTree 8
  openedMaskedZAndLow : Option (PolyVec4 × PolyVec4)
  rejectBit : Bool

/-- Accepted standalone FIPS 204 signature paired with its burned epoch and public transcript view. -/
structure MirRssMlDsaSig where
  cTilde : List UInt8
  z : PolyVec4
  h : Fin 4 → HintTree 8
  usedEpoch : Nat
  attemptLeakage : MirMlDsaAttemptLeakage

/-- Abort classification distinguishing pre-MPC epoch/persistence refusal from an executed MPC
    attempt that opened `(openedMaskedW, openedW1, openedMaskedZAndLow, rejectBit := true)`
    without opening unmasked `z`. -/
inductive MirRssMlDsaAbort where
  | epochReplayOrOverflow
  | attemptRejected (leak : MirMlDsaAttemptLeakage)

/-- Kernel-constructive `UInt64` equality check (`0` axioms). -/
def u64Eq (a b : UInt64) : Bool :=
  match UInt64.decEq a b with
  | isTrue _ => true
  | isFalse _ => false

/-- Non-max `UInt64` epoch check (`checked_add(1).is_some()` in `threshold_mldsa.rs:946`). -/
def u64NotMax (x : UInt64) : Bool := !Nat.beq (x + (1 : UInt64)).toNat 0

private theorem u64_add_one_of_u64NotMax (x : UInt64) (h : u64NotMax x = true) :
    (x + (1 : UInt64)).toNat = x.toNat + 1 := by
  have hOne : (1 : UInt64).toNat = 1 := rfl
  have hMod : (x + (1 : UInt64)).toNat = (x.toNat + 1) % 2 ^ 64 := by
    rw [UInt64.toNat_add, hOne]
  rcases Nat.lt_or_eq_of_le (Nat.succ_le_of_lt x.toNat_lt) with hLt | hEq
  · rw [hMod]
    exact Nat.mod_eq_of_lt hLt
  · exfalso
    have hEqAdd : x.toNat + 1 = 2 ^ 64 := hEq
    have hZeroNat : (x + (1 : UInt64)).toNat = 0 := by
      rw [hMod, hEqAdd]
    unfold u64NotMax at h
    rw [hZeroNat] at h
    cases h

private theorem toNat_u64_of_lt {n : Nat} (hn : n < 18446744073709551616) :
    (UInt64.ofNat n).toNat = n := by
  have h64 : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
  rw [UInt64.toNat_ofNat', h64]
  exact Nat.mod_eq_of_lt hn

private theorem u64_epoch_gate_eq (ep nextEp : UInt64) :
    (u64Eq ep nextEp && u64NotMax nextEp) =
    (Nat.beq ep.toNat nextEp.toNat && u64NotMax ep) := by
  unfold u64Eq
  cases UInt64.decEq ep nextEp with
  | isFalse hNe =>
    cases h2 : Nat.beq ep.toNat nextEp.toNat
    · rfl
    · exfalso
      exact hNe (UInt64.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq (Nat.eq_of_beq_eq_true h2)))
  | isTrue hEq =>
    dsimp only
    rw [hEq, Nat.beq_refl nextEp.toNat]

private def mapRssMlDsaOutcome (o : StepOutcome MirRssMlDsaKeyState MirRssMlDsaSig MirRssMlDsaAbort) :
    StepOutcome SpecRssMlDsaKeyState MirRssMlDsaSig MirRssMlDsaAbort :=
  match o with
  | .ok s' out => .ok s'.toSpec out
  | .err s' e => .err s'.toSpec e

/-- Shared Phase-2/Phase-3 outcome assembler parameterized by the 3 boolean bound verdicts
    (`ct0Ok`, `acceptOk`, `hwOk`), recording exact `MirMlDsaAttemptLeakage` on both accept and abort. -/
def mkRssMlDsaAttemptOutcome {State : Type}
    (stBurned : State)
    (usedEpoch : Nat)
    (cTilde : List UInt8)
    (openedMaskedW z openedZ openedLow : PolyVec4)
    (w1 : Fin 4 → NatTree 8)
    (h : Fin 4 → HintTree 8)
    (ct0Ok acceptOk hwOk : Bool) :
    StepOutcome State MirRssMlDsaSig MirRssMlDsaAbort :=
  if ct0Ok then
    if acceptOk then
      if hwOk then
        .ok stBurned
          { cTilde := cTilde
            z := z
            h := h
            usedEpoch := usedEpoch
            attemptLeakage :=
              { openedMaskedW := openedMaskedW
                openedW1 := w1
                openedMaskedZAndLow := some (openedZ, openedLow)
                rejectBit := false } }
      else
        .err stBurned (.attemptRejected
          { openedMaskedW := openedMaskedW
            openedW1 := w1
            openedMaskedZAndLow := some (openedZ, openedLow)
            rejectBit := true })
    else
      .err stBurned (.attemptRejected
        { openedMaskedW := openedMaskedW
          openedW1 := w1
          openedMaskedZAndLow := some (openedZ, openedLow)
          rejectBit := true })
  else
    .err stBurned (.attemptRejected
      { openedMaskedW := openedMaskedW
        openedW1 := w1
        openedMaskedZAndLow := none
        rejectBit := true })

private theorem mapRssMlDsaOutcome_mk
    (stBurned : MirRssMlDsaKeyState) (stSpecBurned : SpecRssMlDsaKeyState)
    (hBurnEq : stBurned.toSpec = stSpecBurned)
    (usedEpoch : Nat) (cTilde : List UInt8)
    (openedMaskedW z openedZ openedLow : PolyVec4)
    (w1 : Fin 4 → NatTree 8) (h : Fin 4 → HintTree 8)
    (ct0Ok acceptOk hwOk : Bool) :
    mapRssMlDsaOutcome
      (mkRssMlDsaAttemptOutcome stBurned usedEpoch cTilde openedMaskedW z openedZ openedLow w1 h
        ct0Ok acceptOk hwOk) =
    mkRssMlDsaAttemptOutcome stSpecBurned usedEpoch cTilde openedMaskedW z openedZ openedLow w1 h
      ct0Ok acceptOk hwOk := by
  subst hBurnEq
  cases ct0Ok <;> cases acceptOk <;> cases hwOk <;> rfl

/-- Post-epoch-check MIR RSS ML-DSA attempt body evaluating fixed-width `UInt64` norm/hint bounds. -/
def mirRssMlDsaSignBody
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (stBurned : MirRssMlDsaKeyState) (A : PolyMat4) (s1Hat s2Hat : List PolyVec4)
    (inp : MirRssMlDsaAttempt) :
    StepOutcome MirRssMlDsaKeyState MirRssMlDsaSig MirRssMlDsaAbort :=
  let s1 := sumPolyVec4List s1Hat
  let s2 := sumPolyVec4List s2Hat
  let y := sumPolyVec4List inp.yShares
  let t0 := power2RoundLowVec4 (addVec4 (matVecMul4 A s1) s2)
  let w := matVecMul4 A y
  let openedMaskedW := addVec4 w inp.wMask
  let w1 := highBitsVec4 w
  let cTilde := chalHash inp.mu w1
  let c := sampleInBall cTilde
  let ct0 := mulPolyVec4 c t0
  let z := addVec4 y (mulPolyVec4 c s1)
  let u := subVec4 w (mulPolyVec4 c s2)
  let openedZ := addVec4 z inp.zMask
  let openedLow := addVec4 u inp.lowMask
  let h := makeHintVec4 (negVec4 ct0) (addVec4 u ct0)
  let ct0NormU64 : UInt64 := UInt64.ofNat (infNormVec4 ct0)
  let zNormU64 : UInt64 := UInt64.ofNat (infNormVec4 z)
  let uDiffU64 : UInt64 := UInt64.ofNat (centeredDiffNormVec4 u w1)
  let hwU64 : UInt64 := UInt64.ofNat (hintWeightVec4 h)
  mkRssMlDsaAttemptOutcome stBurned inp.epoch.toNat cTilde openedMaskedW z openedZ openedLow w1 h
    (decide (ct0NormU64.toNat < (95232 : UInt64).toNat))
    (decide (zNormU64.toNat < (130994 : UInt64).toNat) &&
     decide (uDiffU64.toNat < (95154 : UInt64).toNat))
    (decide (hwU64.toNat ≤ (80 : UInt64).toNat))

/-- Post-epoch-check specification RSS ML-DSA attempt body over exact `Fq204` / `Nat` bounds. -/
def specRssMlDsaSignBody
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (stBurned : SpecRssMlDsaKeyState) (A : PolyMat4) (s1Hat s2Hat : List PolyVec4)
    (inp : MirRssMlDsaAttempt) :
    StepOutcome SpecRssMlDsaKeyState MirRssMlDsaSig MirRssMlDsaAbort :=
  let s1 := sumPolyVec4List s1Hat
  let s2 := sumPolyVec4List s2Hat
  let y := sumPolyVec4List inp.yShares
  let t0 := power2RoundLowVec4 (addVec4 (matVecMul4 A s1) s2)
  let w := matVecMul4 A y
  let openedMaskedW := addVec4 w inp.wMask
  let w1 := highBitsVec4 w
  let cTilde := chalHash inp.mu w1
  let c := sampleInBall cTilde
  let ct0 := mulPolyVec4 c t0
  let z := addVec4 y (mulPolyVec4 c s1)
  let u := subVec4 w (mulPolyVec4 c s2)
  let openedZ := addVec4 z inp.zMask
  let openedLow := addVec4 u inp.lowMask
  let h := makeHintVec4 (negVec4 ct0) (addVec4 u ct0)
  mkRssMlDsaAttemptOutcome stBurned inp.epoch.toNat cTilde openedMaskedW z openedZ openedLow w1 h
    (decide (infNormVec4 ct0 < mldsa44Gamma2))
    (decide (infNormVec4 z < mldsa44Gamma1 - mldsa44Beta) &&
     decide (centeredDiffNormVec4 u w1 < mldsa44Gamma2 - mldsa44Beta))
    (decide (hintWeightVec4 h ≤ mldsa44Omega))

private theorem mirRssMlDsaSignBody_map_toSpec
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (stBurned : MirRssMlDsaKeyState) (stSpecBurned : SpecRssMlDsaKeyState)
    (hBurnEq : stBurned.toSpec = stSpecBurned)
    (A : PolyMat4) (s1Hat s2Hat : List PolyVec4) (inp : MirRssMlDsaAttempt) :
    mapRssMlDsaOutcome
      (mirRssMlDsaSignBody chalHash sampleInBall stBurned A s1Hat s2Hat inp) =
    specRssMlDsaSignBody chalHash sampleInBall stSpecBurned A s1Hat s2Hat inp := by
  unfold mirRssMlDsaSignBody specRssMlDsaSignBody
  dsimp only
  rw [toNat_u64_of_lt (infNormVec4_lt_u64 _),
      toNat_u64_of_lt (infNormVec4_lt_u64 _),
      toNat_u64_of_lt (centeredDiffNormVec4_lt_u64 _ _),
      toNat_u64_of_lt (hintWeightVec4_lt_u64 _)]
  exact mapRssMlDsaOutcome_mk stBurned stSpecBurned hBurnEq inp.epoch.toNat _ _ _ _ _ _ _ _ _ _

/-- Concrete MIR RSS ML-DSA signing gate evaluating `checked_add(1)` on `nextEpoch : UInt64`
    (`threshold_mldsa.rs:946-948`), fixed-width `UInt64` norm/hint bounds (`95232`, `130994`,
    `95154`, `80`), and explicit Phase-2/Phase-3 `MirMlDsaAttemptLeakage`. -/
def mirRssMlDsaSignStep
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (st : MirRssMlDsaKeyState) (inp : MirRssMlDsaAttempt) :
    StepOutcome MirRssMlDsaKeyState MirRssMlDsaSig MirRssMlDsaAbort :=
  if u64Eq inp.epoch st.nextEpoch && u64NotMax st.nextEpoch then
    mirRssMlDsaSignBody chalHash sampleInBall { st with nextEpoch := st.nextEpoch + 1 }
      st.A st.s1Hat st.s2Hat inp
  else
    .err st .epochReplayOrOverflow

/-- Specification RSS ML-DSA signing step over exact mathematical `Fq204` / `Nat` bounds. -/
def specRssMlDsaSignStep
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (st : SpecRssMlDsaKeyState) (inp : MirRssMlDsaAttempt) :
    StepOutcome SpecRssMlDsaKeyState MirRssMlDsaSig MirRssMlDsaAbort :=
  if Nat.beq inp.epoch.toNat st.nextEpoch && u64NotMax inp.epoch then
    specRssMlDsaSignBody chalHash sampleInBall { st with nextEpoch := st.nextEpoch + 1 }
      st.A st.s1Hat st.s2Hat inp
  else
    .err st .epochReplayOrOverflow

private theorem mirRssMlDsaSignStep_map_toSpec
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (st : MirRssMlDsaKeyState) (inp : MirRssMlDsaAttempt) :
    mapRssMlDsaOutcome (mirRssMlDsaSignStep chalHash sampleInBall st inp) =
    specRssMlDsaSignStep chalHash sampleInBall st.toSpec inp := by
  have hF : ¬ (false = true) := Bool.noConfusion
  have hT : true = true := rfl
  unfold mirRssMlDsaSignStep specRssMlDsaSignStep
  rw [u64_epoch_gate_eq inp.epoch st.nextEpoch]
  have hSpecEp : st.toSpec.nextEpoch = st.nextEpoch.toNat := rfl
  have hSpecA : st.toSpec.A = st.A := rfl
  have hSpecS1 : st.toSpec.s1Hat = st.s1Hat := rfl
  have hSpecS2 : st.toSpec.s2Hat = st.s2Hat := rfl
  rw [hSpecEp, hSpecA, hSpecS1, hSpecS2]
  cases hEp : (Nat.beq inp.epoch.toNat st.nextEpoch.toNat && u64NotMax inp.epoch)
  · rw [ite_eq_right hF, ite_eq_right hF]
    rfl
  · rw [ite_eq_left hT, ite_eq_left hT]
    rcases Bool.and_eq_true_iff.mp hEp with ⟨hBeq, hNotMaxInp⟩
    have hInpEq : inp.epoch = st.nextEpoch :=
      UInt64.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq (Nat.eq_of_beq_eq_true hBeq))
    rw [hInpEq] at hNotMaxInp
    have hAdd1 : (st.nextEpoch + 1).toNat = st.nextEpoch.toNat + 1 :=
      u64_add_one_of_u64NotMax st.nextEpoch hNotMaxInp
    have hBurnEq : ({ st with nextEpoch := st.nextEpoch + 1 } : MirRssMlDsaKeyState).toSpec =
        { st.toSpec with nextEpoch := st.nextEpoch.toNat + 1 } := by
      unfold MirRssMlDsaKeyState.toSpec
      dsimp only
      rw [hAdd1]
    exact mirRssMlDsaSignBody_map_toSpec chalHash sampleInBall
      { st with nextEpoch := st.nextEpoch + 1 }
      { st.toSpec with nextEpoch := st.nextEpoch.toNat + 1 }
      hBurnEq st.A st.s1Hat st.s2Hat inp

def mirRssMlDsaMachine
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256) :
    PartyMachine MirRssMlDsaKeyState MirRssMlDsaAttempt MirRssMlDsaSig :=
  PartyMachine.ofOutcome (mirRssMlDsaSignStep chalHash sampleInBall)

def specRssMlDsaMachine
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256) :
    PartyMachine SpecRssMlDsaKeyState MirRssMlDsaAttempt MirRssMlDsaSig :=
  PartyMachine.ofOutcome (specRssMlDsaSignStep chalHash sampleInBall)

/-- **Bridge 3C (`mirRssMlDsaGate_forwardSim_spec`)**:
    Proves `ForwardSim` from the fixed-width `UInt64` RSS ML-DSA signing gate (`mirRssMlDsaMachine`)
    to `specRssMlDsaMachine` with zero truncation across all `Fq204` norms and `checked_add(1)` epochs. -/
def mirRssMlDsaGate_forwardSim_spec
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256) :
    ForwardSim (mirRssMlDsaMachine chalHash sampleInBall)
               (specRssMlDsaMachine chalHash sampleInBall) :=
  LockstepSim.toForwardSim
    { Inv := fun _ => True
      abs := MirRssMlDsaKeyState.toSpec
      step_eq := fun {st} inp _ => by
        dsimp only [mirRssMlDsaMachine, specRssMlDsaMachine, PartyMachine.ofOutcome]
        have hMap := mirRssMlDsaSignStep_map_toSpec chalHash sampleInBall st inp
        cases hOut : mirRssMlDsaSignStep chalHash sampleInBall st inp with
        | ok s' out =>
          rw [hOut] at hMap
          dsimp only [mapRssMlDsaOutcome] at hMap
          rw [← hMap]
          exact ⟨trivial, rfl⟩
        | err s' e =>
          rw [hOut] at hMap
          dsimp only [mapRssMlDsaOutcome] at hMap
          rw [← hMap]
          exact ⟨trivial, rfl, rfl⟩ }

private theorem specRssMlDsaSignStep_ok_properties
    {chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8}
    {sampleInBall : List UInt8 → Poly256}
    {st st' : SpecRssMlDsaKeyState} {inp : MirRssMlDsaAttempt} {sig : MirRssMlDsaSig}
    (hOk : specRssMlDsaSignStep chalHash sampleInBall st inp = .ok st' sig) :
    st'.nextEpoch = st.nextEpoch + 1 ∧
    sig.usedEpoch = st.nextEpoch ∧
    st'.A = st.A ∧ st'.s1Hat = st.s1Hat ∧ st'.s2Hat = st.s2Hat ∧
    mldsaVerify chalHash sampleInBall st.A
      (power2RoundHighVec4 (addVec4 (matVecMul4 st.A (sumPolyVec4List st.s1Hat))
        (sumPolyVec4List st.s2Hat)))
      inp.mu sig.cTilde sig.z sig.h = true := by
  have hF : ¬ (false = true) := Bool.noConfusion
  have hT : true = true := rfl
  unfold specRssMlDsaSignStep at hOk
  cases hEp : (Nat.beq inp.epoch.toNat st.nextEpoch && u64NotMax inp.epoch)
  · rw [hEp, ite_eq_right hF] at hOk; cases hOk
  · rw [hEp, ite_eq_left hT] at hOk
    rcases Bool.and_eq_true_iff.mp hEp with ⟨hEqBeq, _⟩
    have hEpEq : inp.epoch.toNat = st.nextEpoch := Nat.eq_of_beq_eq_true hEqBeq
    dsimp only [specRssMlDsaSignBody, mkRssMlDsaAttemptOutcome] at hOk
    let s1 := sumPolyVec4List st.s1Hat
    let s2 := sumPolyVec4List st.s2Hat
    let y := sumPolyVec4List inp.yShares
    let t0 := power2RoundLowVec4 (addVec4 (matVecMul4 st.A s1) s2)
    let w := matVecMul4 st.A y
    let w1 := highBitsVec4 w
    let cTilde := chalHash inp.mu w1
    let c := sampleInBall cTilde
    let ct0 := mulPolyVec4 c t0
    let z := addVec4 y (mulPolyVec4 c s1)
    let u := subVec4 w (mulPolyVec4 c s2)
    let h := makeHintVec4 (negVec4 ct0) (addVec4 u ct0)
    cases hCt : decide (infNormVec4 ct0 < mldsa44Gamma2)
    · rw [hCt, ite_eq_right hF] at hOk; cases hOk
    · rw [hCt, ite_eq_left hT] at hOk
      have hCt0Lt : infNormVec4 ct0 < mldsa44Gamma2 := of_decide_eq_true hCt
      cases hAcc : (decide (infNormVec4 z < mldsa44Gamma1 - mldsa44Beta) &&
          decide (centeredDiffNormVec4 u w1 < mldsa44Gamma2 - mldsa44Beta))
      · rw [hAcc, ite_eq_right hF] at hOk; cases hOk
      · rw [hAcc, ite_eq_left hT] at hOk
        rcases Bool.and_eq_true_iff.mp hAcc with ⟨hzB, hDiffB⟩
        have hzLt : infNormVec4 z < mldsa44Gamma1 - mldsa44Beta := of_decide_eq_true hzB
        have hDiffLt : centeredDiffNormVec4 u w1 < mldsa44Gamma2 - mldsa44Beta := of_decide_eq_true hDiffB
        cases hW : decide (hintWeightVec4 h ≤ mldsa44Omega)
        · rw [hW, ite_eq_right hF] at hOk; cases hOk
        · rw [hW, ite_eq_left hT] at hOk
          have hWeightLe : hintWeightVec4 h ≤ mldsa44Omega := of_decide_eq_true hW
          injection hOk with hStEq hSigEq
          subst hStEq hSigEq
          have hB : mldsa44Gamma2 - mldsa44Beta ≤ 95232 := by decide
          obtain ⟨hLowLt, hHighEq⟩ := (centeredDiffNormVec4_lt_iff u w hB).mp hDiffLt
          refine ⟨rfl, hEpEq, rfl, rfl, rfl, ?_⟩
          unfold mldsaVerify
          dsimp only
          have hUseHint := highBits_az_sub_ct_eq_w1 st.A s1 s2 y c mldsa44Beta hLowLt hCt0Lt
          dsimp only at hUseHint
          rw [hUseHint, hHighEq, decide_eq_true hzLt, decide_eq_true hWeightLe, decide_eq_true rfl]
          rfl

private theorem specRssMlDsaMachine_errStep_inv
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (st : SpecRssMlDsaKeyState) (inp : MirRssMlDsaAttempt) :
    st.nextEpoch ≤ ((specRssMlDsaMachine chalHash sampleInBall).errStep st inp).nextEpoch ∧
    ((specRssMlDsaMachine chalHash sampleInBall).errStep st inp).A = st.A ∧
    ((specRssMlDsaMachine chalHash sampleInBall).errStep st inp).s1Hat = st.s1Hat ∧
    ((specRssMlDsaMachine chalHash sampleInBall).errStep st inp).s2Hat = st.s2Hat := by
  have hF : ¬ (false = true) := Bool.noConfusion
  have hT : true = true := rfl
  dsimp only [specRssMlDsaMachine, PartyMachine.ofOutcome]
  cases hOut : specRssMlDsaSignStep chalHash sampleInBall st inp with
  | ok _ _ =>
    obtain ⟨hEp, _, hA, hS1, hS2, _⟩ := specRssMlDsaSignStep_ok_properties hOut
    dsimp only
    exact ⟨by omega, hA, hS1, hS2⟩
  | err _ _ =>
    dsimp only
    unfold specRssMlDsaSignStep at hOut
    cases hEp : (Nat.beq inp.epoch.toNat st.nextEpoch && u64NotMax inp.epoch)
    · rw [hEp, ite_eq_right hF] at hOut
      injection hOut with hStEq _
      subst hStEq
      exact ⟨Nat.le_refl _, rfl, rfl, rfl⟩
    · rw [hEp, ite_eq_left hT] at hOut
      dsimp only [specRssMlDsaSignBody, mkRssMlDsaAttemptOutcome] at hOut
      cases hCt : decide (infNormVec4 (mulPolyVec4 (sampleInBall (chalHash inp.mu
          (highBitsVec4 (matVecMul4 st.A (sumPolyVec4List inp.yShares)))))
          (power2RoundLowVec4 (addVec4 (matVecMul4 st.A (sumPolyVec4List st.s1Hat))
            (sumPolyVec4List st.s2Hat)))) < mldsa44Gamma2)
      · rw [hCt, ite_eq_right hF] at hOut
        injection hOut with hStEq _; subst hStEq
        exact ⟨Nat.le_succ st.nextEpoch, rfl, rfl, rfl⟩
      · rw [hCt, ite_eq_left hT] at hOut
        cases hAcc : (decide (infNormVec4 (addVec4 (sumPolyVec4List inp.yShares)
            (mulPolyVec4 (sampleInBall (chalHash inp.mu
              (highBitsVec4 (matVecMul4 st.A (sumPolyVec4List inp.yShares)))))
              (sumPolyVec4List st.s1Hat))) < mldsa44Gamma1 - mldsa44Beta) &&
          decide (centeredDiffNormVec4 (subVec4 (matVecMul4 st.A (sumPolyVec4List inp.yShares))
            (mulPolyVec4 (sampleInBall (chalHash inp.mu
              (highBitsVec4 (matVecMul4 st.A (sumPolyVec4List inp.yShares)))))
              (sumPolyVec4List st.s2Hat)))
            (highBitsVec4 (matVecMul4 st.A (sumPolyVec4List inp.yShares))) < mldsa44Gamma2 - mldsa44Beta))
        · rw [hAcc, ite_eq_right hF] at hOut
          injection hOut with hStEq _; subst hStEq
          exact ⟨Nat.le_succ st.nextEpoch, rfl, rfl, rfl⟩
        · rw [hAcc, ite_eq_left hT] at hOut
          cases hW : decide (hintWeightVec4 (makeHintVec4
              (negVec4 (mulPolyVec4 (sampleInBall (chalHash inp.mu
                (highBitsVec4 (matVecMul4 st.A (sumPolyVec4List inp.yShares)))))
                (power2RoundLowVec4 (addVec4 (matVecMul4 st.A (sumPolyVec4List st.s1Hat))
                  (sumPolyVec4List st.s2Hat)))))
              (addVec4 (subVec4 (matVecMul4 st.A (sumPolyVec4List inp.yShares))
                (mulPolyVec4 (sampleInBall (chalHash inp.mu
                  (highBitsVec4 (matVecMul4 st.A (sumPolyVec4List inp.yShares)))))
                  (sumPolyVec4List st.s2Hat)))
                (mulPolyVec4 (sampleInBall (chalHash inp.mu
                  (highBitsVec4 (matVecMul4 st.A (sumPolyVec4List inp.yShares)))))
                  (power2RoundLowVec4 (addVec4 (matVecMul4 st.A (sumPolyVec4List st.s1Hat))
                    (sumPolyVec4List st.s2Hat)))))) ≤ mldsa44Omega)
          · rw [hW, ite_eq_right hF] at hOut
            injection hOut with hStEq _; subst hStEq
            exact ⟨Nat.le_succ st.nextEpoch, rfl, rfl, rfl⟩
          · rw [hW, ite_eq_left hT] at hOut; cases hOut

private theorem specRssMlDsaMachine_trace_sound
    {chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8}
    {sampleInBall : List UInt8 → Poly256}
    {st₀ stF : SpecRssMlDsaKeyState}
    {tr : List (MirRssMlDsaAttempt × MirRssMlDsaSig)}
    (hTr : (specRssMlDsaMachine chalHash sampleInBall).ValidTrace st₀ tr stF) :
    (∀ p ∈ tr, st₀.nextEpoch ≤ p.2.usedEpoch) ∧
    tr.Pairwise (fun p₁ p₂ => p₁.2.usedEpoch ≠ p₂.2.usedEpoch) ∧
    (∀ p ∈ tr,
      mldsaVerify chalHash sampleInBall st₀.A
        (power2RoundHighVec4 (addVec4 (matVecMul4 st₀.A (sumPolyVec4List st₀.s1Hat))
          (sumPolyVec4List st₀.s2Hat)))
        p.1.mu p.2.cTilde p.2.z p.2.h = true) := by
  induction hTr with
  | nil =>
    exact ⟨(fun _ hm => nomatch hm), List.Pairwise.nil, (fun _ hm => nomatch hm)⟩
  | @accept sCur sNext _ inp sig rest hStep _ ih =>
    dsimp only [specRssMlDsaMachine, PartyMachine.ofOutcome] at hStep
    cases hOut : specRssMlDsaSignStep chalHash sampleInBall sCur inp with
    | err _ _ => rw [hOut] at hStep; cases hStep
    | ok sOk sigOk =>
      rw [hOut] at hStep
      injection hStep with hP
      rcases Prod.mk.inj hP with ⟨rfl, rfl⟩
      obtain ⟨hNextEp, hUsedEp, hA, hS1, hS2, hVerHead⟩ := specRssMlDsaSignStep_ok_properties hOut
      obtain ⟨hGeTail, hPairTail, hVerTail⟩ := ih
      refine ⟨?_, List.Pairwise.cons ?_ hPairTail, ?_⟩
      · intro p hp
        rcases List.mem_cons.mp hp with rfl | hMem
        · dsimp only; omega
        · have h1 := hGeTail p hMem; omega
      · intro p₂ hp₂
        have h1 := hGeTail p₂ hp₂
        dsimp only; omega
      · intro p hp
        rcases List.mem_cons.mp hp with rfl | hMem
        · exact hVerHead
        · have hV := hVerTail p hMem
          rwa [hA, hS1, hS2] at hV
  | @reject sCur _ inp rest _ _ ih =>
    obtain ⟨hEpLe, hA, hS1, hS2⟩ := specRssMlDsaMachine_errStep_inv chalHash sampleInBall sCur inp
    obtain ⟨hGeTail, hPairTail, hVerTail⟩ := ih
    refine ⟨fun p hp => ?_, hPairTail, fun p hp => ?_⟩
    · have h1 := hGeTail p hp; omega
    · have hV := hVerTail p hp
      rwa [hA, hS1, hS2] at hV

/-- **Explicit Leakage-Bounded RSS ML-DSA Rejection & Multi-Turn FIPS 204 Soundness
    (`mirRssMlDsaGate_leakage_bounded_and_fips204_sound`)**:
    1. **Mask-Space Uniformity (`rssMaskVec4Equiv`)**: Every Phase-1/Phase-3 masked vector opened
       during a rejected or accepted attempt (`w + wMask`, `z + zMask`, `u + lowMask`) is a
       constructive `SimpleEquiv` bijection of its conversion mask (`0` secret leakage beyond
       `(openedW1, rejectBit)` when masks are uniform).
    2. **Explicit Rejected-Attempt Leakage & Unreleased `z`**: Whenever `ct0`, `z`, `LowBits(u)`,
       `HighBits(u) ≠ w1`, or `weight(h) > 80` rejects an epoch-valid attempt, `mirRssMlDsaMachine`
       withholds unmasked `z` (`step = none`), burns `nextEpoch := nextEpoch + 1`, and records the
       exact `MirMlDsaAttemptLeakage` with `openedW1 = HighBits(w)` and `rejectBit = true`.
    3. **Multi-Turn Epoch Uniqueness & Standalone FIPS 204 `mldsaVerify` Soundness**: Across any
       multi-turn `ValidTrace` of `mirRssMlDsaMachine`, every emitted signature uses a strictly
       distinct `usedEpoch` and passes standalone `mldsaVerify` under the reconstructed public key. -/
theorem mirRssMlDsaGate_leakage_bounded_and_fips204_sound
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256) :
    (∀ v : PolyVec4, Nonempty (SimpleEquiv PolyVec4 PolyVec4) ∧
      ∀ mask : PolyVec4, (rssMaskVec4Equiv v).invFun ((rssMaskVec4Equiv v).toFun mask) = mask) ∧
    (∀ (st : MirRssMlDsaKeyState) (inp : MirRssMlDsaAttempt),
      let s1 := sumPolyVec4List st.s1Hat
      let s2 := sumPolyVec4List st.s2Hat
      let y := sumPolyVec4List inp.yShares
      let w := matVecMul4 st.A y
      let c := sampleInBall (chalHash inp.mu (highBitsVec4 w))
      let ct0 := mulPolyVec4 c (power2RoundLowVec4 (addVec4 (matVecMul4 st.A s1) s2))
      let z := addVec4 y (mulPolyVec4 c s1)
      let u := subVec4 w (mulPolyVec4 c s2)
      let h := makeHintVec4 (negVec4 ct0) (addVec4 u ct0)
      (u64Eq inp.epoch st.nextEpoch && u64NotMax st.nextEpoch) = true →
      (¬ (infNormVec4 ct0 < mldsa44Gamma2) ∨
       ¬ (infNormVec4 z < mldsa44Gamma1 - mldsa44Beta) ∨
       ¬ (lowBitsNormVec4 u < mldsa44Gamma2 - mldsa44Beta) ∨
       highBitsVec4 u ≠ highBitsVec4 w ∨
       ¬ (hintWeightVec4 h ≤ mldsa44Omega)) →
      (mirRssMlDsaMachine chalHash sampleInBall).step st inp = none ∧
      ((mirRssMlDsaMachine chalHash sampleInBall).errStep st inp).nextEpoch = st.nextEpoch + 1 ∧
      ∃ leak : MirMlDsaAttemptLeakage,
        mirRssMlDsaSignStep chalHash sampleInBall st inp =
          .err { st with nextEpoch := st.nextEpoch + 1 } (.attemptRejected leak) ∧
        leak.openedW1 = highBitsVec4 w ∧
        leak.rejectBit = true) ∧
    (∀ {st₀ stFinal : MirRssMlDsaKeyState}
       {trace : List (MirRssMlDsaAttempt × MirRssMlDsaSig)},
      (mirRssMlDsaMachine chalHash sampleInBall).ValidTrace st₀ trace stFinal →
      trace.Pairwise (fun p₁ p₂ => p₁.2.usedEpoch ≠ p₂.2.usedEpoch) ∧
      (∀ p ∈ trace,
        mldsaVerify chalHash sampleInBall st₀.A
          (power2RoundHighVec4 (addVec4 (matVecMul4 st₀.A (sumPolyVec4List st₀.s1Hat))
            (sumPolyVec4List st₀.s2Hat)))
          p.1.mu p.2.cTilde p.2.z p.2.h = true)) := by
  refine ⟨fun v => ⟨⟨rssMaskVec4Equiv v⟩, (rssMaskVec4Equiv v).left_inv⟩, ?_, ?_⟩
  · intro st inp s1 s2 y w c ct0 z u h hEpValid hRej
    have hF : ¬ (false = true) := Bool.noConfusion
    have hT : true = true := rfl
    dsimp only [mirRssMlDsaMachine, PartyMachine.ofOutcome]
    unfold mirRssMlDsaSignStep
    rw [hEpValid, ite_eq_left hT]
    dsimp only [mirRssMlDsaSignBody, mkRssMlDsaAttemptOutcome]
    rw [toNat_u64_of_lt (infNormVec4_lt_u64 _),
        toNat_u64_of_lt (infNormVec4_lt_u64 _),
        toNat_u64_of_lt (centeredDiffNormVec4_lt_u64 _ _),
        toNat_u64_of_lt (hintWeightVec4_lt_u64 _)]
    cases hCtB : decide (infNormVec4 ct0 < (95232 : UInt64).toNat)
    · rw [ite_eq_right hF]
      exact ⟨rfl, rfl, _, rfl, rfl, rfl⟩
    · rw [ite_eq_left hT]
      have hCtLt : infNormVec4 ct0 < mldsa44Gamma2 := of_decide_eq_true hCtB
      cases hAccB : (decide (infNormVec4 z < (130994 : UInt64).toNat) &&
          decide (centeredDiffNormVec4 u (highBitsVec4 w) < (95154 : UInt64).toNat))
      · rw [ite_eq_right hF]
        exact ⟨rfl, rfl, _, rfl, rfl, rfl⟩
      · rw [ite_eq_left hT]
        rcases Bool.and_eq_true_iff.mp hAccB with ⟨hzB, hDiffB⟩
        have hzLt : infNormVec4 z < mldsa44Gamma1 - mldsa44Beta := of_decide_eq_true hzB
        have hDiffLt : centeredDiffNormVec4 u (highBitsVec4 w) < mldsa44Gamma2 - mldsa44Beta :=
          of_decide_eq_true hDiffB
        have hB : mldsa44Gamma2 - mldsa44Beta ≤ 95232 := by decide
        obtain ⟨hLowLt, hHighEq⟩ := (centeredDiffNormVec4_lt_iff u w hB).mp hDiffLt
        cases hWB : decide (hintWeightVec4 h ≤ (80 : UInt64).toNat)
        · rw [ite_eq_right hF]
          exact ⟨rfl, rfl, _, rfl, rfl, rfl⟩
        · have hWeightLe : hintWeightVec4 h ≤ mldsa44Omega := of_decide_eq_true hWB
          rcases hRej with h1 | h2 | h3 | h4 | h5
          · exact False.elim (h1 hCtLt)
          · exact False.elim (h2 hzLt)
          · exact False.elim (h3 hLowLt)
          · exact False.elim (h4 hHighEq)
          · exact False.elim (h5 hWeightLe)
  · intro st₀ stFinal trace hTrace
    have hRel₀ : (mirRssMlDsaGate_forwardSim_spec chalHash sampleInBall).Rel st₀ st₀.toSpec :=
      ⟨trivial, rfl⟩
    obtain ⟨_, hSpecTr, _⟩ :=
      (mirRssMlDsaGate_forwardSim_spec chalHash sampleInBall).lift_validTrace hRel₀ hTrace
    obtain ⟨_, hPair, hVer⟩ := specRssMlDsaMachine_trace_sound hSpecTr
    exact ⟨hPair, hVer⟩

/-! ## §4. Certified `2 * q > n + f` `BeltLatch` Guard $\to$ `WalLatchState` & `IdealTsig` Bridge -/

def finMemBool {n : Nat} (x : Fin n) : List (Fin n) → Bool
  | [] => false
  | y :: ys => (x.val == y.val) || finMemBool x ys

private theorem finMemBool_eq_true_iff {n : Nat} (x : Fin n) :
    ∀ (ys : List (Fin n)), finMemBool x ys = true ↔ x ∈ ys
  | [] => by simp [finMemBool]
  | y :: ys => by
    simp only [finMemBool, Bool.or_eq_true, finMemBool_eq_true_iff x ys, List.mem_cons]
    constructor
    · rintro (hEq | hRest)
      · exact .inl (Fin.ext (Nat.eq_of_beq_eq_true hEq))
      · exact .inr hRest
    · rintro (rfl | hRest)
      · exact .inl (Nat.beq_refl _)
      · exact .inr hRest

private def finAll : (n : Nat) → List (Fin n)
  | 0 => []
  | n + 1 => ⟨0, Nat.zero_lt_succ n⟩ :: (finAll n).map (fun i => ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)

private theorem finAll_length : ∀ (n : Nat), (finAll n).length = n
  | 0 => rfl
  | n + 1 => by simp [finAll, finAll_length n]

private theorem mem_finAll : ∀ {n : Nat} (x : Fin n), x ∈ finAll n
  | 0, x => absurd x.isLt (Nat.not_lt_zero _)
  | n + 1, ⟨0, _⟩ => .head _
  | n + 1, ⟨k + 1, hk⟩ => by
    simp only [finAll, List.mem_cons, List.mem_map]
    exact .inr ⟨⟨k, Nat.lt_of_succ_lt_succ hk⟩, mem_finAll ⟨k, Nat.lt_of_succ_lt_succ hk⟩, rfl⟩

private theorem length_erase_add_one {α : Type} [BEq α] [LawfulBEq α] :
    ∀ {x : α} {ys : List α}, x ∈ ys → (ys.erase x).length + 1 = ys.length
  | _, [], h => nomatch h
  | x, y :: ys, h => by
    simp only [List.erase_cons]
    cases hxy : (y == x)
    · rcases List.mem_cons.mp h with rfl | hTail
      · rw [beq_self_eq_true] at hxy; cases hxy
      · simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons]
        have ih := length_erase_add_one hTail
        omega
    · simp

private theorem mem_erase_of_ne_local {α : Type} [BEq α] [LawfulBEq α] :
    ∀ {z x : α} {ys : List α}, z ≠ x → z ∈ ys → z ∈ ys.erase x
  | _, _, [], _, h => nomatch h
  | z, x, y :: ys, hNe, hMem => by
    simp only [List.erase_cons]
    cases hxy : (y == x)
    · rcases List.mem_cons.mp hMem with rfl | hTail
      · exact .head _
      · exact .tail _ (mem_erase_of_ne_local hNe hTail)
    · have hyx : y = x := eq_of_beq hxy
      subst hyx
      rcases List.mem_cons.mp hMem with rfl | hTail
      · exact False.elim (hNe rfl)
      · exact hTail

private theorem nodup_length_le_subset_decEq {α : Type} [DecidableEq α] :
    ∀ {xs ys : List α}, xs.Nodup → (∀ x ∈ xs, x ∈ ys) → xs.length ≤ ys.length
  | [], _, _, _ => Nat.zero_le _
  | x :: xs, ys, hNd, hSub => by
    rcases List.nodup_cons.mp hNd with ⟨hxNot, hNdTail⟩
    have hxIn : x ∈ ys := hSub x (.head _)
    have hSubErase : ∀ z ∈ xs, z ∈ ys.erase x := by
      intro z hz
      have hNe : z ≠ x := fun hEq => hxNot (hEq ▸ hz)
      exact mem_erase_of_ne_local hNe (hSub z (.tail _ hz))
    have ih := nodup_length_le_subset_decEq hNdTail hSubErase
    have hLen := length_erase_add_one hxIn
    simp only [List.length_cons]
    omega

/-- The counting bound at `Fin n`, with the structural `instDecidableEqFin` equality test (the
    default `BEq (Fin n)` found through the order hierarchy carries a classical lawfulness proof). -/
private theorem nodup_length_le_subset_fin {n : Nat} {xs ys : List (Fin n)}
    (hNd : xs.Nodup) (hSub : ∀ x ∈ xs, x ∈ ys) : xs.length ≤ ys.length :=
  @nodup_length_le_subset_decEq (Fin n) (instDecidableEqFin n) xs ys hNd hSub

private theorem filter_compl_length {α : Type} (p : α → Bool) :
    ∀ (xs : List α), (xs.filter p).length + (xs.filter (fun x => !p x)).length = xs.length
  | [] => rfl
  | x :: xs => by
    have ih := filter_compl_length p xs
    cases hp : p x
    · rw [List.filter_cons_of_neg (by rw [hp]; decide), List.filter_cons_of_pos (by rw [hp]; rfl)]
      simp only [List.length_cons]
      omega
    · rw [List.filter_cons_of_pos hp, List.filter_cons_of_neg (by rw [hp]; decide)]
      simp only [List.length_cons]
      omega

private theorem mem_of_mem_filter_local {α : Type} {p : α → Bool} :
    ∀ {x : α} {xs : List α}, x ∈ xs.filter p → x ∈ xs
  | _, [], h => nomatch h
  | x, y :: ys, h => by
    cases hp : p y
    · rw [List.filter_cons_of_neg (by rw [hp]; decide)] at h
      exact .tail _ (mem_of_mem_filter_local h)
    · rw [List.filter_cons_of_pos hp] at h
      rcases List.mem_cons.mp h with rfl | hTail
      · exact .head _
      · exact .tail _ (mem_of_mem_filter_local hTail)

private theorem pred_of_mem_filter_local {α : Type} (p : α → Bool) :
    ∀ {x : α} {xs : List α}, x ∈ xs.filter p → p x = true
  | _, [], h => nomatch h
  | x, y :: ys, h => by
    cases hp : p y
    · rw [List.filter_cons_of_neg (by rw [hp]; decide)] at h
      exact pred_of_mem_filter_local p h
    · rw [List.filter_cons_of_pos hp] at h
      rcases List.mem_cons.mp h with rfl | hTail
      · exact hp
      · exact pred_of_mem_filter_local p hTail

private theorem nodup_filter_local {α : Type} (p : α → Bool) :
    ∀ {xs : List α}, xs.Nodup → (xs.filter p).Nodup
  | [], _ => .nil
  | x :: xs, hNd => by
    rcases List.nodup_cons.mp hNd with ⟨hxNot, hNdTail⟩
    have ih := nodup_filter_local p hNdTail
    cases hp : p x
    · rw [List.filter_cons_of_neg (by rw [hp]; decide)]
      exact ih
    · rw [List.filter_cons_of_pos hp, List.nodup_cons]
      refine ⟨fun hIn => hxNot (mem_of_mem_filter_local hIn), ih⟩

private theorem nodup_append_disjoint {α : Type} :
    ∀ {xs ys : List α}, xs.Nodup → ys.Nodup → (∀ x ∈ xs, x ∉ ys) → (xs ++ ys).Nodup
  | [], ys, _, hYs, _ => hYs
  | x :: xs, ys, hXs, hYs, hDisj => by
    rcases List.nodup_cons.mp hXs with ⟨hxNotXs, hXsTail⟩
    simp only [List.cons_append, List.nodup_cons, List.mem_append, not_or]
    exact ⟨⟨hxNotXs, hDisj x (.head _)⟩,
      nodup_append_disjoint hXsTail hYs (fun z hz => hDisj z (.tail _ hz))⟩

/-- Constructive search (`0 Classical.choice`) locating the first validator `p ∈ Q₁` that also
    belongs to `Q₂` and is non-corrupt (`p ∉ corrupt`). -/
def findHonestQuorumIntersector {n : Nat}
    (corrupt Q₁ Q₂ : List (Fin n)) : Option (Fin n) :=
  Q₁.find? (fun p => finMemBool p Q₂ && !finMemBool p corrupt)

/-- **Bridge 4A (`beltLatch_quorum_intersection_honest_witness`, `0 Classical.choice`)**:
    Whenever `2 * q > n + f`, `corrupt.length ≤ f`, and `Q₁, Q₂ : List (Fin n)` are duplicate-free
    `q`-quorums (`q ≤ Q₁.length`, `q ≤ Q₂.length`), `findHonestQuorumIntersector` constructively
    returns `some p` with `p ∈ Q₁ ∧ p ∈ Q₂ ∧ p ∉ corrupt`. -/
def extractBeltLatchHonestIntersector {n q f : Nat}
    (corrupt Q₁ Q₂ : List (Fin n))
    (hBound : n + f < 2 * q)
    (hCorruptLe : corrupt.length ≤ f)
    (hNd₁ : Q₁.Nodup) (hNd₂ : Q₂.Nodup)
    (hLen₁ : q ≤ Q₁.length) (hLen₂ : q ≤ Q₂.length) :
    { p : Fin n // p ∈ Q₁ ∧ p ∈ Q₂ ∧ p ∉ corrupt } :=
  match hFind : findHonestQuorumIntersector corrupt Q₁ Q₂ with
  | some p =>
    ⟨p, by
      have hMem := List.mem_of_find?_eq_some hFind
      have hPred := List.find?_some hFind
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hPred
      have hpQ2 : p ∈ Q₂ := (finMemBool_eq_true_iff p Q₂).mp hPred.1
      have hpNotC : p ∉ corrupt := fun hc => by
        rw [(finMemBool_eq_true_iff p corrupt).mpr hc] at hPred
        cases hPred.2
      exact ⟨hMem, hpQ2, hpNotC⟩⟩
  | none =>
    False.elim <| by
      have hNoneAll := List.find?_eq_none.mp hFind
      let inQ2 := Q₁.filter (fun p => finMemBool p Q₂)
      let outQ2 := Q₁.filter (fun p => !finMemBool p Q₂)
      have hPart : inQ2.length + outQ2.length = Q₁.length :=
        filter_compl_length (fun p => finMemBool p Q₂) Q₁
      have hInSubCorrupt : ∀ p ∈ inQ2, p ∈ corrupt := by
        intro p hpIn
        have hpQ1 : p ∈ Q₁ := mem_of_mem_filter_local hpIn
        have hpB2 : finMemBool p Q₂ = true :=
          pred_of_mem_filter_local (fun q => finMemBool q Q₂) hpIn
        have hFalse := hNoneAll p hpQ1
        rw [hpB2, Bool.true_and] at hFalse
        cases hC : finMemBool p corrupt
        · rw [hC] at hFalse; exact False.elim (hFalse rfl)
        · exact (finMemBool_eq_true_iff p corrupt).mp hC
      have hInLe : inQ2.length ≤ corrupt.length :=
        nodup_length_le_subset_fin (nodup_filter_local _ hNd₁) hInSubCorrupt
      have hDisjOut : ∀ p ∈ outQ2, p ∉ Q₂ := by
        intro p hpOut hpIn2
        have hNotB : (!finMemBool p Q₂) = true :=
          pred_of_mem_filter_local (fun q => !finMemBool q Q₂) hpOut
        rw [(finMemBool_eq_true_iff p Q₂).mpr hpIn2] at hNotB
        cases hNotB
      have hUnionNd : (outQ2 ++ Q₂).Nodup :=
        nodup_append_disjoint (nodup_filter_local _ hNd₁) hNd₂ hDisjOut
      have hUnionLe : (outQ2 ++ Q₂).length ≤ (finAll n).length :=
        nodup_length_le_subset_fin hUnionNd (fun x _ => mem_finAll x)
      rw [List.length_append, finAll_length] at hUnionLe
      omega

theorem beltLatch_quorum_intersection_honest_witness {n q f : Nat}
    (corrupt Q₁ Q₂ : List (Fin n))
    (hBound : n + f < 2 * q)
    (hCorruptLe : corrupt.length ≤ f)
    (hNd₁ : Q₁.Nodup) (hNd₂ : Q₂.Nodup)
    (hLen₁ : q ≤ Q₁.length) (hLen₂ : q ≤ Q₂.length) :
    ∃ p : Fin n,
      findHonestQuorumIntersector corrupt Q₁ Q₂ = some p ∧
      p ∈ Q₁ ∧ p ∈ Q₂ ∧ p ∉ corrupt := by
  let ⟨p, hp1, hp2, hpNotC⟩ :=
    extractBeltLatchHonestIntersector corrupt Q₁ Q₂ hBound hCorruptLe hNd₁ hNd₂ hLen₁ hLen₂
  cases hOpt : findHonestQuorumIntersector corrupt Q₁ Q₂ with
  | some q0 =>
    have hMem := List.mem_of_find?_eq_some hOpt
    have hPred := List.find?_some hOpt
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hPred
    have hq2 : q0 ∈ Q₂ := (finMemBool_eq_true_iff q0 Q₂).mp hPred.1
    have hqNotC : q0 ∉ corrupt := fun hc => by
      rw [(finMemBool_eq_true_iff q0 corrupt).mpr hc] at hPred
      cases hPred.2
    exact ⟨q0, rfl, hMem, hq2, hqNotC⟩
  | none =>
    have hFalse := (List.find?_eq_none.mp hOpt) p hp1
    have hb2 : finMemBool p Q₂ = true := (finMemBool_eq_true_iff p Q₂).mpr hp2
    have hbC : finMemBool p corrupt = false := by
      cases hc : finMemBool p corrupt
      · rfl
      · exact False.elim (hpNotC ((finMemBool_eq_true_iff p corrupt).mp hc))
    rw [hb2, hbC] at hFalse
    exact False.elim (hFalse rfl)

/-- **`#tooth` (`tooth_subthreshold_beltLatch_quorum_allows_split_brain`)**:
    When `2 * q ≤ n + f` (`n = 4, f = 1, q = 2`, so `2 * 2 = 4 ≤ 5`), two duplicate-free `q = 2`
    quorums `Q₁ = [0, 1]` and `Q₂ = [0, 2]` intersect ONLY at the single Byzantine node
    `corrupt = [0]` (`findHonestQuorumIntersector = none`), permitting split-brain epoch signing! -/
theorem tooth_subthreshold_beltLatch_quorum_allows_split_brain :
    let corrupt : List (Fin 4) := [⟨0, by decide⟩]
    let Q₁ : List (Fin 4) := [⟨0, by decide⟩, ⟨1, by decide⟩]
    let Q₂ : List (Fin 4) := [⟨0, by decide⟩, ⟨2, by decide⟩]
    2 * 2 ≤ 4 + 1 ∧
    corrupt.length ≤ 1 ∧
    Q₁.Nodup ∧ Q₂.Nodup ∧
    2 ≤ Q₁.length ∧ 2 ≤ Q₂.length ∧
    findHonestQuorumIntersector corrupt Q₁ Q₂ = none := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, rfl⟩

/-- Hand-written model of a `q`-of-`n` belt latch: exactly the fields of `WalLatchState`, gated by
    an authenticated quorum certificate. It is not extracted from Rust, and it is not the
    production `crates/qsag-core/src/belt_latch.rs` (a fixed 2-of-3 latch with pairwise echo
    MACs). The MIR-extracted `q`-of-`n` guard is `authenticated_belt.VerifiedBeltQuorumGuard`;
    its theorems live in `aeneas/lean/QsagVerified/Proofs/PantsAndQuorumGuards.lean`. -/
structure MirBeltLatchState where
  enrolledPkDigest : List UInt8
  nextEpoch : Nat
  latchedRecord : Option (Nat × List UInt8 × ByteArray)
  poisoned : Bool
  deriving DecidableEq

/-- Field-for-field reading of a `MirBeltLatchState` as a `WalLatchState`. -/
def MirBeltLatchState.toWal (st : MirBeltLatchState) : WalLatchState :=
  ⟨st.enrolledPkDigest, st.nextEpoch, st.latchedRecord, st.poisoned⟩

/-- Epoch-commit request carrying an authenticated quorum certificate: one `(custodian, ackTag)`
    entry per acknowledging custodian. -/
structure BeltLatchCommitReq (n : Nat) where
  pkDigest : List UInt8
  reqEpoch : Nat
  msgDigest : List UInt8
  freshSig : ByteArray
  quorumCert : List (Fin n × List UInt8)
  deriving DecidableEq

/-- Custodians named by a certificate, in order. -/
def BeltLatchCommitReq.signers {n : Nat} (req : BeltLatchCommitReq n) : List (Fin n) :=
  req.quorumCert.map Prod.fst

/-- Certificate gate. `verifyAck p epoch msgDigest tag` is the per-custodian acknowledgment
    verifier (a MAC check under custodian `p`'s enrolled key); it is a parameter of the model, not
    something this file computes. The gate requires every entry to verify for this request's
    `(reqEpoch, msgDigest)`, the named custodians to be pairwise distinct, and at least `q`
    entries. -/
def beltCertAuthenticated {n : Nat} (verifyAck : Fin n → Nat → List UInt8 → List UInt8 → Bool)
    (q : Nat) (req : BeltLatchCommitReq n) : Bool :=
  req.quorumCert.all (fun e => verifyAck e.1 req.reqEpoch req.msgDigest e.2) &&
    decide req.signers.Nodup && decide (q ≤ req.quorumCert.length)

/-- `MirBeltLatchState` transition: check the authenticated certificate, then run
    `walCommitBeforeRelease`. A rejected request leaves the state unchanged. -/
def mirBeltLatchStep {n : Nat} (verifyAck : Fin n → Nat → List UInt8 → List UInt8 → Bool)
    (q : Nat) (st : MirBeltLatchState) (req : BeltLatchCommitReq n) :
    StepOutcome MirBeltLatchState ByteArray Unit :=
  if !beltCertAuthenticated verifyAck q req then
    .err st ()
  else
    match walCommitBeforeRelease st.toWal req.pkDigest req.reqEpoch req.msgDigest req.freshSig with
    | .err _ _ => .err st ()
    | .ok wal' sig =>
      .ok ⟨wal'.enrolledPkDigest, wal'.nextEpoch, wal'.latchedRecord, wal'.poisoned⟩ sig

/-- `PartyMachine` for `MirBeltLatchState`. -/
@[expose]
def mirBeltLatchMachine {n : Nat} (verifyAck : Fin n → Nat → List UInt8 → List UInt8 → Bool)
    (q : Nat) : PartyMachine MirBeltLatchState (BeltLatchCommitReq n) ByteArray :=
  PartyMachine.ofOutcome (mirBeltLatchStep verifyAck q)

/-- Protocol-level `WalLatchState` machine behind the same authenticated certificate gate. -/
def specWalLatchMachine {n : Nat} (verifyAck : Fin n → Nat → List UInt8 → List UInt8 → Bool)
    (q : Nat) : PartyMachine WalLatchState (BeltLatchCommitReq n) ByteArray :=
  PartyMachine.ofOutcome fun wal req =>
    if !beltCertAuthenticated verifyAck q req then
      .err wal ()
    else
      match walCommitBeforeRelease wal req.pkDigest req.reqEpoch req.msgDigest req.freshSig with
      | .err _ _ => .err wal ()
      | .ok wal' sig => .ok wal' sig

/-- **Bridge 4B (`mirBeltLatch_forwardSim_walLatch`).**
    The abstraction map is the field-for-field `MirBeltLatchState.toWal`, so the simulation of
    transitions is definitional. What this proves beyond that is the invariant: the simulation
    relation is `st.toWal.WellFormed ∧ st.toWal = wal`, and `WalLatchState.WellFormed` (32-byte
    enrolled digest, latched epoch strictly below `nextEpoch`) is shown preserved by every accepted
    and every rejected step via `walCommitBeforeRelease_preserves_wellFormed`. -/
def mirBeltLatch_forwardSim_walLatch {n : Nat}
    (verifyAck : Fin n → Nat → List UInt8 → List UInt8 → Bool) (q : Nat) :
    ForwardSim (mirBeltLatchMachine verifyAck q) (specWalLatchMachine verifyAck q) :=
  LockstepSim.toForwardSim
    { Inv := fun st => st.toWal.WellFormed
      abs := MirBeltLatchState.toWal
      step_eq := fun {st} req hWf => by
        dsimp only [mirBeltLatchMachine, specWalLatchMachine, PartyMachine.ofOutcome]
        unfold mirBeltLatchStep
        cases hCert : beltCertAuthenticated verifyAck q req
        · exact ⟨hWf, rfl, rfl⟩
        · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          cases hCommit : walCommitBeforeRelease st.toWal req.pkDigest req.reqEpoch
              req.msgDigest req.freshSig with
          | err _ _ => exact ⟨hWf, rfl, rfl⟩
          | ok wal' sig =>
            exact ⟨(walCommitBeforeRelease_preserves_wellFormed hWf hCommit).1, rfl⟩ }

/-- Along any multi-turn trace of `mirBeltLatchMachine` from a well-formed state, the final state
    is well-formed. -/
theorem mirBeltLatch_trace_preserves_wellFormed {n : Nat}
    (verifyAck : Fin n → Nat → List UInt8 → List UInt8 → Bool) (q : Nat)
    {st st_f : MirBeltLatchState} {trace : List (BeltLatchCommitReq n × ByteArray)}
    (hWf : st.toWal.WellFormed)
    (hTrace : (mirBeltLatchMachine verifyAck q).ValidTrace st trace st_f) :
    st_f.toWal.WellFormed := by
  obtain ⟨_, _, hRel⟩ :=
    (mirBeltLatch_forwardSim_walLatch verifyAck q).lift_validTrace
      (a₀ := st.toWal) ⟨hWf, rfl⟩ hTrace
  exact hRel.1

/-- **Authenticated quorum intersection.** Two certificates that both pass
    `beltCertAuthenticated` under `2 * q > n + f` share a custodian outside the corrupt set whose
    acknowledgment tag verifies in each: an honest custodian acknowledged both requests. -/
theorem beltCert_authenticated_quorums_share_honest_signer {n q f : Nat}
    (verifyAck : Fin n → Nat → List UInt8 → List UInt8 → Bool)
    (corrupt : List (Fin n)) (req₁ req₂ : BeltLatchCommitReq n)
    (hBound : n + f < 2 * q) (hCorruptLe : corrupt.length ≤ f)
    (h₁ : beltCertAuthenticated verifyAck q req₁ = true)
    (h₂ : beltCertAuthenticated verifyAck q req₂ = true) :
    ∃ (p : Fin n) (tag₁ tag₂ : List UInt8), p ∉ corrupt ∧
      (p, tag₁) ∈ req₁.quorumCert ∧ (p, tag₂) ∈ req₂.quorumCert ∧
      verifyAck p req₁.reqEpoch req₁.msgDigest tag₁ = true ∧
      verifyAck p req₂.reqEpoch req₂.msgDigest tag₂ = true := by
  simp only [beltCertAuthenticated, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
    at h₁ h₂
  obtain ⟨⟨hAll₁, hNd₁⟩, hLen₁⟩ := h₁
  obtain ⟨⟨hAll₂, hNd₂⟩, hLen₂⟩ := h₂
  have hL₁ : q ≤ req₁.signers.length := by
    unfold BeltLatchCommitReq.signers
    rw [List.length_map]
    exact hLen₁
  have hL₂ : q ≤ req₂.signers.length := by
    unfold BeltLatchCommitReq.signers
    rw [List.length_map]
    exact hLen₂
  obtain ⟨p, _, hp₁, hp₂, hpC⟩ :=
    beltLatch_quorum_intersection_honest_witness corrupt req₁.signers req₂.signers
      hBound hCorruptLe hNd₁ hNd₂ hL₁ hL₂
  unfold BeltLatchCommitReq.signers at hp₁ hp₂
  obtain ⟨e₁, he₁, hEq₁⟩ := List.mem_map.mp hp₁
  obtain ⟨e₂, he₂, hEq₂⟩ := List.mem_map.mp hp₂
  subst hEq₁
  refine ⟨e₁.1, e₁.2, e₂.2, hpC, he₁, ?_, hAll₁ e₁ he₁, ?_⟩
  · rw [← hEq₂]
    exact he₂
  · rw [← hEq₂]
    exact hAll₂ e₂ he₂

/-- **`#tooth`**: a certificate containing a tag that fails verification is rejected, however many
    entries it has. -/
theorem tooth_beltCert_forged_tag_rejected {n : Nat}
    (verifyAck : Fin n → Nat → List UInt8 → List UInt8 → Bool) (q : Nat)
    (req : BeltLatchCommitReq n) (e : Fin n × List UInt8) (he : e ∈ req.quorumCert)
    (hForged : verifyAck e.1 req.reqEpoch req.msgDigest e.2 = false) :
    beltCertAuthenticated verifyAck q req = false := by
  cases h : beltCertAuthenticated verifyAck q req
  · rfl
  · simp only [beltCertAuthenticated, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
    exact absurd (h.1.1 e he) (by rw [hForged]; decide)

/-- **`#tooth`**: a certificate naming the same custodian twice is rejected even when both tags
    verify, so one custodian cannot be counted twice toward `q`. -/
theorem tooth_beltCert_duplicate_signer_rejected {n : Nat}
    (verifyAck : Fin n → Nat → List UInt8 → List UInt8 → Bool) (q : Nat)
    (req : BeltLatchCommitReq n) (p : Fin n) (t₁ t₂ : List UInt8)
    (rest : List (Fin n × List UInt8))
    (hCert : req.quorumCert = (p, t₁) :: (p, t₂) :: rest) :
    beltCertAuthenticated verifyAck q req = false := by
  cases h : beltCertAuthenticated verifyAck q req
  · rfl
  · simp only [beltCertAuthenticated, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
    have hNd := h.1.2
    unfold BeltLatchCommitReq.signers at hNd
    rw [hCert] at hNd
    simp only [List.map_cons] at hNd
    exact absurd List.mem_cons_self (List.nodup_cons.mp hNd).1

/-- Connects a `2 * q > n + f`-certified `BeltLatch` quorum directly to `IdealTsig`'s
    `validThresholdApproval = true` and `thresholdApproval_requires_honest_party`! -/
theorem mirBeltLatch_quorum_discharges_idealTsig_approval {PK Msg : Type}
    {n q f : Nat}
    (corrupt : List (Fin n))
    (quorum : List (Fin n))
    (st : IdealTsigState PK Msg)
    (hNP : st.numParties = n)
    (hTh : st.threshold = q)
    (hQPos : 0 < q) (hQLeN : q ≤ n)
    (hCorruptEq : st.corruptParties = corrupt.map Fin.val)
    (hNoCheaters : st.identifiedCheaters = [])
    (hCorruptNd : corrupt.Nodup)
    (hCorruptLe : corrupt.length ≤ f)
    (hBound : n + f < 2 * q)
    (hQuorumNd : quorum.Nodup)
    (hQuorumLen : q ≤ quorum.length) :
    let honestApprovers := (quorum.filter (fun p => !finMemBool p corrupt)).map Fin.val
    validThresholdApproval st honestApprovers = true ∧
    (∃ h ∈ honestApprovers, h < st.numParties ∧ h ∉ st.corruptParties) := by
  intro honestApprovers
  have hFinValInj : ∀ {a b : Fin n}, a.val = b.val → a = b := fun h => Fin.ext h
  have hMapNodup : ∀ {xs : List (Fin n)}, xs.Nodup → (xs.map Fin.val).Nodup := by
    intro xs hNd
    induction xs with
    | nil => exact .nil
    | cons x xs ih =>
      rcases List.nodup_cons.mp hNd with ⟨hxNot, hTail⟩
      simp only [List.map_cons, List.nodup_cons, List.mem_map]
      refine ⟨?_, ih hTail⟩
      rintro ⟨y, hyMem, hyEq⟩
      exact hxNot (hFinValInj hyEq ▸ hyMem)
  have hValid : validThresholdApproval st honestApprovers = true := by
    unfold validThresholdApproval
    rw [hNP, hTh, hCorruptEq, hNoCheaters]
    simp only [List.not_mem_nil, not_false_eq_true, decide_true, Bool.and_true]
    rw [List.filter_eq_self.mpr (fun _ _ => rfl)]
    have hThOk : 0 < q ∧ q ≤ n := ⟨hQPos, hQLeN⟩
    have hCNd : (corrupt.map Fin.val).Nodup := hMapNodup hCorruptNd
    have hCRange : (corrupt.map Fin.val).all (fun c => decide (c < n)) = true := by
      rw [List.all_eq_true]
      intro c hc
      rcases List.mem_map.mp hc with ⟨p, _, rfl⟩
      exact decide_eq_true p.isLt
    have hHonFiltNd : (quorum.filter (fun p => !finMemBool p corrupt)).Nodup :=
      nodup_filter_local _ hQuorumNd
    have hHonNd : honestApprovers.Nodup := hMapNodup hHonFiltNd
    have hHonAll :
        honestApprovers.all (fun h => decide (h < n) && decide (h ∉ corrupt.map Fin.val)) = true := by
      rw [List.all_eq_true]
      intro h hh
      rcases List.mem_map.mp hh with ⟨p, hpFilt, rfl⟩
      have hNotB : (!finMemBool p corrupt) = true :=
        pred_of_mem_filter_local (fun q => !finMemBool q corrupt) hpFilt
      have hpNotC : p.val ∉ corrupt.map Fin.val := by
        intro hInMap
        rcases List.mem_map.mp hInMap with ⟨c, hcMem, hcVal⟩
        have hpc : p = c := Fin.ext hcVal.symm
        subst hpc
        rw [(finMemBool_eq_true_iff p corrupt).mpr hcMem] at hNotB
        cases hNotB
      simp [p.isLt, hpNotC]
    have hPart := filter_compl_length (fun p => finMemBool p corrupt) quorum
    have hInCSub : ∀ p ∈ quorum.filter (fun p => finMemBool p corrupt), p ∈ corrupt :=
      fun p hp => (finMemBool_eq_true_iff p corrupt).mp
        (pred_of_mem_filter_local (fun q => finMemBool q corrupt) hp)
    have hInCLe : (quorum.filter (fun p => finMemBool p corrupt)).length ≤ corrupt.length :=
      nodup_length_le_subset_fin (nodup_filter_local _ hQuorumNd) hInCSub
    have hSumGe :
        q ≤ (corrupt.map Fin.val).length + honestApprovers.length := by
      dsimp only [honestApprovers]
      rw [List.length_map, List.length_map]
      omega
    rw [decide_eq_true hThOk, decide_eq_true hCNd, hCRange,
        decide_eq_true hHonNd, hHonAll, decide_eq_true hSumGe]
    have hCLt : (corrupt.map Fin.val).length < q := by
      rw [List.length_map]
      omega
    have hHonPos : 0 < honestApprovers.length := by omega
    rw [decide_eq_true hCLt, decide_eq_true hHonPos]
    rfl
  have hDishonestBound : st.corruptParties.length + 1 ≤ st.threshold := by
    rw [hCorruptEq, List.length_map, hTh]
    omega
  exact ⟨hValid, thresholdApproval_requires_honest_party st honestApprovers hDishonestBound hValid⟩

/-! ## §5. Conditional 4-Layer Control-Flow & Authorization Refinement Chain (`isa_to_mir_to_protocol_to_ideal_sim`) -/

/-- Domain/capacity separation block `"QSAGR1CM"` (`rate = 8, capacity = 4, sep = 1`) for Round-1
    width-12 `Poseidon2` weighted-feed-forward commitments. -/
def round1CommitDomainBlock : Lane4 :=
  ⟨Goldilocks.ofNat 0x515341475231434D, Goldilocks.ofNat 8, Goldilocks.ofNat 4, Goldilocks.one⟩

/-- Canonical width-12 `Poseidon2` commitment input state placing `(nonceLimb, maskLimb, sessionTag, partyId)`
    in rate block `b0`, 4 full `Goldilocks` blinding limbs `blind` (~256 bits of hiding randomness)
    in rate block `b1`, and fixed domain/capacity block `round1CommitDomainBlock` in `b2`. -/
def round1CommitState12 (nonceLimb maskLimb sessionTag partyId : Goldilocks) (blind : Lane4) :
    Poseidon2State12 :=
  ⟨⟨nonceLimb, maskLimb, sessionTag, partyId⟩, blind, round1CommitDomainBlock⟩

theorem round1CommitState12_injective
    {n₁ m₁ s₁ p₁ n₂ m₂ s₂ p₂ : Goldilocks} {b₁ b₂ : Lane4}
    (h : round1CommitState12 n₁ m₁ s₁ p₁ b₁ = round1CommitState12 n₂ m₂ s₂ p₂ b₂) :
    n₁ = n₂ ∧ m₁ = m₂ ∧ s₁ = s₂ ∧ p₁ = p₂ ∧ b₁ = b₂ := by
  injection h with hb0 hb1 _
  injection hb0 with hn hm hs hp
  exact ⟨hn, hm, hs, hp, hb1⟩

/-- Concrete algebraic Round-1 commitment opening over the full 30-round width-12 `Poseidon2`
    weighted compression `poseidon2CompressWeighted`: commits to `(nonceLimb, maskLimb, sessionTag, partyId)` together with
    4 full `Goldilocks` blinding limbs `blind : Lane4`. Hiding is not proved; this is a
    model commitment, without a byte-level refinement to the deployed commitment construction. -/
structure Round1Opening where
  committedB0 : Lane4
  nonceLimb : Goldilocks
  maskLimb : Goldilocks
  sessionTag : Goldilocks
  partyId : Goldilocks
  blind : Lane4
  deriving DecidableEq

/-- Evaluate the deployed 30-round width-12 `Poseidon2` compression with weighted feed-forward,
    `poseidon2CompressWeighted st = (poseidon2Perm12 st).b0 + st.b0 + 2·st.b1 + 4·st.b2`, returning
    the 4-limb (`256`-bit) digest `Lane4`. -/
def computeRound1CommitB0 (nonceLimb maskLimb sessionTag partyId : Goldilocks) (blind : Lane4) : Lane4 :=
  poseidon2CompressWeighted (round1CommitState12 nonceLimb maskLimb sessionTag partyId blind)

/-- Verify a single Round-1 commitment opening by recomputing `computeRound1CommitB0`. -/
def verifyRound1Opening (op : Round1Opening) : Bool :=
  decide (op.committedB0 =
    computeRound1CommitB0 op.nonceLimb op.maskLimb op.sessionTag op.partyId op.blind)

theorem verifyRound1Opening_of_eq {op : Round1Opening}
    (h : op.committedB0 =
      computeRound1CommitB0 op.nonceLimb op.maskLimb op.sessionTag op.partyId op.blind) :
    verifyRound1Opening op = true := by
  unfold verifyRound1Opening
  exact decide_eq_true h

/-- Concrete collision witness against the deployed 30-round width-12 `Poseidon2` weighted
    compression: two distinct domain-framed 12-limb states `st₁ ≠ st₂` (whose permutation outputs
    are also distinct by `poseidon2Perm12_bijective`) colliding on `poseidon2CompressWeighted`. -/
structure Round1CommitCollisionWitness where
  st₁ : Poseidon2State12
  st₂ : Poseidon2State12
  neState : st₁ ≠ st₂
  nePerm : poseidon2Perm12 st₁ ≠ poseidon2Perm12 st₂
  dom₁ : st₁.b2 = round1CommitDomainBlock
  dom₂ : st₂.b2 = round1CommitDomainBlock
  eqCommitB0 : poseidon2CompressWeighted st₁ = poseidon2CompressWeighted st₂

/-- **Constructive Commitment Binding (`extractRound1CommitCollision`, `0 Classical.choice`)**:
    Any two distinct verified `Round1Opening`s sharing `committedB0` constructively produce a
    concrete `Round1CommitCollisionWitness` against the 30-round `poseidon2CompressWeighted`
    compression. -/
def extractRound1CommitCollision (op₁ op₂ : Round1Opening)
    (hSameCommit : op₁.committedB0 = op₂.committedB0)
    (hVer₁ : verifyRound1Opening op₁ = true)
    (hVer₂ : verifyRound1Opening op₂ = true)
    (hNe : op₁ ≠ op₂) :
    Round1CommitCollisionWitness :=
  let st₁ := round1CommitState12 op₁.nonceLimb op₁.maskLimb op₁.sessionTag op₁.partyId op₁.blind
  let st₂ := round1CommitState12 op₂.nonceLimb op₂.maskLimb op₂.sessionTag op₂.partyId op₂.blind
  have hNeSt : st₁ ≠ st₂ := fun hEq => by
    obtain ⟨hn, hm, hs, hp, hb⟩ := round1CommitState12_injective hEq
    cases op₁; cases op₂
    dsimp only at hSameCommit hn hm hs hp hb
    subst hSameCommit hn hm hs hp hb
    exact hNe rfl
  have hEq1 : op₁.committedB0 = poseidon2CompressWeighted st₁ :=
    of_decide_eq_true hVer₁
  have hEq2 : op₂.committedB0 = poseidon2CompressWeighted st₂ :=
    of_decide_eq_true hVer₂
  { st₁ := st₁
    st₂ := st₂
    neState := hNeSt
    nePerm := fun hPermEq => hNeSt ((poseidon2Perm12_bijective st₁ st₂).2.2.1.mp hPermEq)
    dom₁ := rfl
    dom₂ := rfl
    eqCommitB0 := hEq1.symm.trans (hSameCommit.trans hEq2) }

theorem round1Commit_binding (op₁ op₂ : Round1Opening)
    (hSameCommit : op₁.committedB0 = op₂.committedB0)
    (hVer₁ : verifyRound1Opening op₁ = true)
    (hVer₂ : verifyRound1Opening op₂ = true) :
    op₁ = op₂ ∨ Nonempty Round1CommitCollisionWitness := by
  if hEq : op₁ = op₂ then
    exact .inl hEq
  else
    exact .inr ⟨extractRound1CommitCollision op₁ op₂ hSameCommit hVer₁ hVer₂ hEq⟩

private theorem nodup_length_le_subset_nat :
    ∀ {xs ys : List Nat}, xs.Nodup → (∀ x ∈ xs, x ∈ ys) → xs.length ≤ ys.length
  | [], _, _, _ => Nat.zero_le _
  | x :: xs, ys, hNd, hSub => by
    rcases List.nodup_cons.mp hNd with ⟨hxNot, hNdTail⟩
    have hxIn : x ∈ ys := hSub x (.head _)
    have hSubErase : ∀ z ∈ xs, z ∈ ys.erase x := by
      intro z hz
      have hNe : z ≠ x := fun hEq => hxNot (hEq ▸ hz)
      exact mem_erase_of_ne_local hNe (hSub z (.tail _ hz))
    have ih := nodup_length_le_subset_nat hNdTail hSubErase
    have hLen := length_erase_add_one hxIn
    simp only [List.length_cons]
    omega

private theorem nodup_map_of_inj_on {α β : Type} (f : α → β) :
    ∀ {xs : List α}, xs.Nodup → (∀ x ∈ xs, ∀ y ∈ xs, f x = f y → x = y) → (xs.map f).Nodup
  | [], _, _ => .nil
  | x :: xs, hNd, hInj => by
    rcases List.nodup_cons.mp hNd with ⟨hxNot, hTail⟩
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, nodup_map_of_inj_on f hTail
      (fun a ha b hb hEq => hInj a (.tail _ ha) b (.tail _ hb) hEq)⟩
    intro hMem
    rcases List.mem_map.mp hMem with ⟨y, hyMem, hyEq⟩
    exact hxNot (hInj x (.head _) y (.tail _ hyMem) hyEq.symm ▸ hyMem)

private theorem mul_add_lt_mul {a A r p : Nat} (ha : a < A) (hr : r < p) :
    a * p + r < A * p := by
  have hLe : (a + 1) * p ≤ A * p := Nat.mul_le_mul_right p ha
  rw [Nat.add_mul, Nat.one_mul] at hLe
  omega

private theorem mul_add_mod_div (q : Nat) {r p : Nat} (hr : r < p) :
    (q * p + r) % p = r ∧ (q * p + r) / p = q := by
  have hp : 0 < p := Nat.lt_of_le_of_lt (Nat.zero_le r) hr
  have hComm : q * p + r = r + p * q := by rw [Nat.mul_comm, Nat.add_comm]
  rw [hComm]
  exact ⟨by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr],
         by rw [Nat.add_mul_div_left r q hp, Nat.div_eq_of_lt hr, Nat.zero_add]⟩

/-- Canonical base-`p` bijection from `Lane4` onto `[0, p^4)`. -/
def encodeLane4Nat (L : Lane4) : Nat :=
  (((L.x0.val * goldilocksPrime + L.x1.val) * goldilocksPrime + L.x2.val) * goldilocksPrime) +
    L.x3.val

theorem encodeLane4Nat_lt (L : Lane4) : encodeLane4Nat L < goldilocksPrime ^ 4 := by
  unfold encodeLane4Nat
  have h1 : L.x0.val * goldilocksPrime + L.x1.val < goldilocksPrime * goldilocksPrime :=
    mul_add_lt_mul L.x0.isLt L.x1.isLt
  have h2 : (L.x0.val * goldilocksPrime + L.x1.val) * goldilocksPrime + L.x2.val <
      (goldilocksPrime * goldilocksPrime) * goldilocksPrime :=
    mul_add_lt_mul h1 L.x2.isLt
  have h3 : ((L.x0.val * goldilocksPrime + L.x1.val) * goldilocksPrime + L.x2.val) *
      goldilocksPrime + L.x3.val <
      ((goldilocksPrime * goldilocksPrime) * goldilocksPrime) * goldilocksPrime :=
    mul_add_lt_mul h2 L.x3.isLt
  have hPow : ((goldilocksPrime * goldilocksPrime) * goldilocksPrime) * goldilocksPrime =
      goldilocksPrime ^ 4 := by
    simp [Nat.pow_succ, Nat.pow_zero]
  exact hPow ▸ h3

theorem encodeLane4Nat_injective {L₁ L₂ : Lane4}
    (h : encodeLane4Nat L₁ = encodeLane4Nat L₂) : L₁ = L₂ := by
  unfold encodeLane4Nat at h
  have h3a := mul_add_mod_div
    ((L₁.x0.val * goldilocksPrime + L₁.x1.val) * goldilocksPrime + L₁.x2.val) L₁.x3.isLt
  have h3b := mul_add_mod_div
    ((L₂.x0.val * goldilocksPrime + L₂.x1.val) * goldilocksPrime + L₂.x2.val) L₂.x3.isLt
  have hx3 : L₁.x3.val = L₂.x3.val := by
    have hm := congrArg (· % goldilocksPrime) h
    rwa [h3a.1, h3b.1] at hm
  have hq2 : (L₁.x0.val * goldilocksPrime + L₁.x1.val) * goldilocksPrime + L₁.x2.val =
      (L₂.x0.val * goldilocksPrime + L₂.x1.val) * goldilocksPrime + L₂.x2.val := by
    have hd := congrArg (· / goldilocksPrime) h
    rwa [h3a.2, h3b.2] at hd
  have h2a := mul_add_mod_div (L₁.x0.val * goldilocksPrime + L₁.x1.val) L₁.x2.isLt
  have h2b := mul_add_mod_div (L₂.x0.val * goldilocksPrime + L₂.x1.val) L₂.x2.isLt
  have hx2 : L₁.x2.val = L₂.x2.val := by
    have hm := congrArg (· % goldilocksPrime) hq2
    rwa [h2a.1, h2b.1] at hm
  have hq1 : L₁.x0.val * goldilocksPrime + L₁.x1.val = L₂.x0.val * goldilocksPrime + L₂.x1.val := by
    have hd := congrArg (· / goldilocksPrime) hq2
    rwa [h2a.2, h2b.2] at hd
  have h1a := mul_add_mod_div L₁.x0.val L₁.x1.isLt
  have h1b := mul_add_mod_div L₂.x0.val L₂.x1.isLt
  have hx1 : L₁.x1.val = L₂.x1.val := by
    have hm := congrArg (· % goldilocksPrime) hq1
    rwa [h1a.1, h1b.1] at hm
  have hx0 : L₁.x0.val = L₂.x0.val := by
    have hd := congrArg (· / goldilocksPrime) hq1
    rwa [h1a.2, h1b.2] at hd
  exact Lane4.ext (Goldilocks.ext hx0) (Goldilocks.ext hx1) (Goldilocks.ext hx2) (Goldilocks.ext hx3)

private def decodeOpening5Nat (k : Nat) : Goldilocks × Lane4 :=
  let p := goldilocksPrime
  let n := Goldilocks.ofNat k
  let k1 := k / p
  let d3 := Goldilocks.ofNat k1
  let d2 := Goldilocks.ofNat (k1 / p)
  let d1 := Goldilocks.ofNat (k1 / p / p)
  let d0 := Goldilocks.ofNat (k1 / p / p / p)
  (n, ⟨d0, d1, d2, d3⟩)

private theorem div_lt_of_lt_mul_right {a c p : Nat} (h : a < c * p) : a / p < c := by
  if hGe : c ≤ a / p then
    have hMul : c * p ≤ (a / p) * p := Nat.mul_le_mul_right p hGe
    have hDivMod : p * (a / p) + a % p = a := Nat.div_add_mod a p
    rw [Nat.mul_comm p (a / p)] at hDivMod
    omega
  else
    omega

private theorem div_mul_add_mod_right (x p : Nat) : (x / p) * p + x % p = x := by
  rw [Nat.mul_comm (x / p) p]
  exact Nat.div_add_mod x p

private theorem decodeOpening5Nat_reconstruct {k : Nat} (hk : k < goldilocksPrime ^ 5) :
    let (n, b) := decodeOpening5Nat k
    encodeLane4Nat b * goldilocksPrime + n.val = k := by
  dsimp only [decodeOpening5Nat, encodeLane4Nat, Goldilocks.ofNat]
  let p := goldilocksPrime
  have hPow5 : goldilocksPrime ^ 5 = (((p * p) * p) * p) * p := by
    dsimp only [p]; simp [Nat.pow_succ, Nat.pow_zero]
  have hk1 : k / p < ((p * p) * p) * p := div_lt_of_lt_mul_right (hPow5 ▸ hk)
  have hk2 : k / p / p < (p * p) * p := div_lt_of_lt_mul_right hk1
  have hk3 : k / p / p / p < p * p := div_lt_of_lt_mul_right hk2
  have hk4 : k / p / p / p / p < p := div_lt_of_lt_mul_right hk3
  change (((((k / p / p / p / p) % p * p + (k / p / p / p) % p) * p +
    (k / p / p) % p) * p + (k / p) % p) * p + k % p) = k
  rw [Nat.mod_eq_of_lt hk4,
      div_mul_add_mod_right (k / p / p / p) p,
      div_mul_add_mod_right (k / p / p) p,
      div_mul_add_mod_right (k / p) p,
      div_mul_add_mod_right k p]

/-- **Hiding Space Cardinality Bound (`round1Commit_hiding_space_exceeds_digest`)**:
    The 4-limb blinding space `Lane4` exceeds $2^{255}$ (`2 ^ 255 < p ^ 4`), the 6-limb secret
    `(nonceLimb, maskLimb, blind)` space strictly exceeds the 4-limb digest space (`p ^ 4 < p ^ 6`),
    and the full 8-limb opening+blinding rate space satisfies `p ^ 4 < p ^ 8`. -/
theorem round1Commit_hiding_space_exceeds_digest :
    2 ^ 255 < goldilocksPrime ^ 4 ∧
    goldilocksPrime ^ 4 < goldilocksPrime ^ 6 ∧
    goldilocksPrime ^ 4 < goldilocksPrime ^ 8 := by
  refine ⟨by decide, by decide, by decide⟩

/-- **Pigeonhole Non-Invertibility (`round1Commit_no_algebraic_inverse`)**:
    Because the opening+blinding domain strictly exceeds the 4-limb `Lane4` digest space, NO
    function `recover : Lane4 → Goldilocks × Goldilocks × Lane4` can invert `computeRound1CommitB0`
    to recover `(nonceLimb, maskLimb, blind)` for any `(sessionTag, partyId)`. -/
theorem round1Commit_no_algebraic_inverse
    (sessionTag partyId : Goldilocks)
    (recover : Lane4 → Goldilocks × Goldilocks × Lane4) :
    ¬ (∀ (nonceLimb maskLimb : Goldilocks) (blind : Lane4),
        recover (computeRound1CommitB0 nonceLimb maskLimb sessionTag partyId blind) =
          (nonceLimb, maskLimb, blind)) := by
  intro hRec
  let B := goldilocksPrime ^ 4
  have hLePow5 : B + 1 ≤ goldilocksPrime ^ 5 := by
    dsimp only [B]; decide
  let f : Nat → Nat := fun k =>
    let nb := decodeOpening5Nat k
    encodeLane4Nat (computeRound1CommitB0 nb.1 Goldilocks.zero sessionTag partyId nb.2)
  have hInjOn : ∀ x ∈ List.range (B + 1), ∀ y ∈ List.range (B + 1), f x = f y → x = y := by
    intro x hx y hy hEq
    have hx5 : x < goldilocksPrime ^ 5 := Nat.lt_of_lt_of_le (List.mem_range.mp hx) hLePow5
    have hy5 : y < goldilocksPrime ^ 5 := Nat.lt_of_lt_of_le (List.mem_range.mp hy) hLePow5
    have hCommitEq :
        computeRound1CommitB0 (decodeOpening5Nat x).1 Goldilocks.zero sessionTag partyId (decodeOpening5Nat x).2 =
        computeRound1CommitB0 (decodeOpening5Nat y).1 Goldilocks.zero sessionTag partyId (decodeOpening5Nat y).2 :=
      encodeLane4Nat_injective hEq
    have hRecEq := congrArg recover hCommitEq
    rw [hRec, hRec] at hRecEq
    injection hRecEq with hn hRest
    injection hRest with _ hb
    have hPairEq : decodeOpening5Nat x = decodeOpening5Nat y := Prod.ext hn hb
    have hxRec := decodeOpening5Nat_reconstruct hx5
    have hyRec := decodeOpening5Nat_reconstruct hy5
    dsimp only at hxRec hyRec
    rw [hPairEq] at hxRec
    exact hxRec.symm.trans hyRec
  have hMapNd : ((List.range (B + 1)).map f).Nodup :=
    nodup_map_of_inj_on f (Constructive.nodup_range (B + 1)) hInjOn
  have hSub : ∀ z ∈ (List.range (B + 1)).map f, z ∈ List.range B := by
    intro z hz
    rcases List.mem_map.mp hz with ⟨k, _, rfl⟩
    exact List.mem_range.mpr (encodeLane4Nat_lt _)
  have hLenLe := nodup_length_le_subset_nat hMapNd hSub
  rw [List.length_map, List.length_range, List.length_range] at hLenLe
  omega

/-- Retired 1-round `sbox7` + `applyME` encoding (retained strictly for `#tooth` regression). -/
def retiredOneRoundApplyMECommitB0 (nonceLimb maskLimb sessionTag partyId : Goldilocks) : Lane4 :=
  let dom := Goldilocks.ofNat 0x515341475231434D
  let st : Poseidon2State12 :=
    ⟨⟨sbox7 nonceLimb, sbox7 maskLimb, sbox7 sessionTag, sbox7 partyId⟩,
     ⟨dom, Goldilocks.one, Goldilocks.zero, Goldilocks.zero⟩,
     ⟨Goldilocks.zero, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩⟩
  (applyME st).b0

private def lane4SubCoord (a b : Lane4) : Lane4 :=
  ⟨Goldilocks.sub a.x0 b.x0, Goldilocks.sub a.x1 b.x1,
   Goldilocks.sub a.x2 b.x2, Goldilocks.sub a.x3 b.x3⟩

private def sboxLane4InvCoord (b : Lane4) : Lane4 :=
  ⟨sbox7Inv b.x0, sbox7Inv b.x1, sbox7Inv b.x2, sbox7Inv b.x3⟩

/-- Numerator of the `4 × 4` solve below: `8u` from `e`. -/
private def oneRoundSolve8 (e : Lane4) : Lane4 :=
  ⟨Goldilocks.sub (Goldilocks.sub (Goldilocks.sub (Goldilocks.mul (Goldilocks.ofNat 9) e.x0) e.x1) e.x2)
     (Goldilocks.mul (Goldilocks.ofNat 12) e.x3),
   Goldilocks.sub (Goldilocks.sub (Goldilocks.mul (Goldilocks.ofNat 3) e.x1) e.x2) e.x0,
   Goldilocks.sub (Goldilocks.sub (Goldilocks.mul (Goldilocks.ofNat 3) e.x2) e.x1) e.x0,
   Goldilocks.sub (Goldilocks.mul (Goldilocks.ofNat 8) e.x3) (Goldilocks.mul (Goldilocks.ofNat 4) e.x0)⟩

/-- Explicit algebraic inverse of the retired 1-round formula under the deployed `M_4 ⊗ P_3`
    external layer. With `u = x^{∘7}` and `e = c - (applyME ⟨0, d, 0⟩).b0`,
    `e₀ = 4u₀+2u₁+2u₂+6u₃`, `e₁ = 2u₀+4u₁+2u₂+3u₃`, `e₂ = 2u₀+2u₁+4u₂+3u₃`, `e₃ = 2u₀+u₁+u₂+4u₃`,
    a linear system of determinant `32` solved by
    `8u = (9e₀-e₁-e₂-12e₃, 3e₁-e₂-e₀, 3e₂-e₁-e₀, 8e₃-4e₀)`; the opening is `u^{∘ d_inv}`. -/
def invertOneRoundApplyMECommitB0 (c : Lane4) : Lane4 :=
  let dom := Goldilocks.ofNat 0x515341475231434D
  let d : Lane4 := ⟨dom, Goldilocks.one, Goldilocks.zero, Goldilocks.zero⟩
  let inv8G : Goldilocks := Goldilocks.ofNat 16140901060737761281
  sboxLane4InvCoord (lane4Scale inv8G (oneRoundSolve8 (lane4SubCoord c
    (applyME ⟨⟨Goldilocks.zero, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩, d,
      ⟨Goldilocks.zero, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩⟩).b0)))

private theorem inv8G_mul_eight_cancel (x : Goldilocks) :
    Goldilocks.mul (Goldilocks.ofNat 16140901060737761281) (Goldilocks.mul (Goldilocks.ofNat 8) x) = x := by
  change CommRingOps.mul (Goldilocks.ofNat 16140901060737761281)
    (CommRingOps.mul (Goldilocks.ofNat 8) x) = x
  rw [← LawfulCommRing.mul_assoc]
  have hOne : CommRingOps.mul (Goldilocks.ofNat 16140901060737761281) (Goldilocks.ofNat 8) =
      CommRingOps.one := by decide
  rw [hOne]
  exact LawfulCommRing.one_mul x

private theorem oneRound_linear_extract (u d : Lane4) :
    oneRoundSolve8 (lane4SubCoord
      (applyME ⟨u, d, ⟨Goldilocks.zero, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩⟩).b0
      (applyME ⟨⟨Goldilocks.zero, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩, d,
        ⟨Goldilocks.zero, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩⟩).b0) =
      lane4Scale (Goldilocks.ofNat 8) u := by
  unfold oneRoundSolve8 lane4SubCoord applyME poseidon2Transpose3x4 poseidon2Transpose4x3
    applyMEStd applyM4 lane4Sum
  simp only [lane4Add_eq, lane4Scale_eq]
  have hz : Goldilocks.zero = goldOfInt 0 := rfl
  apply Lane4.ext <;>
    (dsimp only;
     rw [← goldOfInt_nat u.x0, ← goldOfInt_nat u.x1, ← goldOfInt_nat u.x2, ← goldOfInt_nat u.x3,
         ← goldOfInt_nat d.x0, ← goldOfInt_nat d.x1, ← goldOfInt_nat d.x2, ← goldOfInt_nat d.x3];
     simp only [hz, ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_sub, goldOfInt_mul];
     congr 1; omega)

/-- **`#tooth` Regression (`tooth_one_round_applyME_commitment_exposes_opening`)**:
    Proves that the retired unblinded 1-round encoding `(applyME ⟨x^{∘7}, d, 0⟩).b0` is
    algebraically inverted by `invertOneRoundApplyMECommitB0` on EVERY 4-limb opening, and concretely recovers `[17, 23, 31, 47]` from its commitment. -/
theorem tooth_one_round_applyME_commitment_exposes_opening :
    (∀ nonceLimb maskLimb sessionTag partyId : Goldilocks,
      invertOneRoundApplyMECommitB0
        (retiredOneRoundApplyMECommitB0 nonceLimb maskLimb sessionTag partyId) =
        ⟨nonceLimb, maskLimb, sessionTag, partyId⟩) ∧
    invertOneRoundApplyMECommitB0
      (retiredOneRoundApplyMECommitB0
        (Goldilocks.ofNat 17) (Goldilocks.ofNat 23) (Goldilocks.ofNat 31) (Goldilocks.ofNat 47)) =
      ⟨Goldilocks.ofNat 17, Goldilocks.ofNat 23, Goldilocks.ofNat 31, Goldilocks.ofNat 47⟩ := by
  have hAll : ∀ nonceLimb maskLimb sessionTag partyId : Goldilocks,
      invertOneRoundApplyMECommitB0
        (retiredOneRoundApplyMECommitB0 nonceLimb maskLimb sessionTag partyId) =
        ⟨nonceLimb, maskLimb, sessionTag, partyId⟩ := by
    intro n m s p
    unfold invertOneRoundApplyMECommitB0 retiredOneRoundApplyMECommitB0
    dsimp only
    rw [oneRound_linear_extract]
    simp only [lane4Scale_eq]
    unfold sboxLane4InvCoord
    dsimp only
    rw [inv8G_mul_eight_cancel, inv8G_mul_eight_cancel, inv8G_mul_eight_cancel,
      inv8G_mul_eight_cancel]
    exact Lane4.ext (sbox7Inv_sbox7 n) (sbox7Inv_sbox7 m) (sbox7Inv_sbox7 s) (sbox7Inv_sbox7 p)
  exact ⟨hAll, hAll (Goldilocks.ofNat 17) (Goldilocks.ofNat 23) (Goldilocks.ofNat 31) (Goldilocks.ofNat 47)⟩

/-- Domain separation tag `"QSAG.MIR.POSEIDON2.MAC.V1"` for full-key, full-message 32-byte `Poseidon2` tags. -/
def poseidon2MacDomainTag : List UInt8 :=
  [0x51, 0x53, 0x41, 0x47, 0x2E, 0x4D, 0x49, 0x52,
   0x2E, 0x50, 0x4F, 0x53, 0x45, 0x49, 0x44, 0x4F,
   0x4E, 0x32, 0x2E, 0x4D, 0x41, 0x43, 0x2E, 0x56, 0x31]

/-- Canonical length-framed preimage absorbing `poseidon2MacDomainTag`, every byte of `sh`,
    and every byte of `msg`. -/
def poseidon2FullTagPreimage (sh msg : List UInt8) : List UInt8 :=
  encodeMultiFrame [poseidon2MacDomainTag, sh, msg]

/-- Full-key, full-message test tag over length-framed `[poseidon2MacDomainTag, sh, msg]`.
    This prefix-keyed hash has no proved MAC unforgeability here. Four-layer instantiations using
    it witness conditional control-flow refinement, not cryptographic signing security. -/
def poseidon2TagBytes (sh msg : List UInt8) : ByteArray :=
  packWire (poseidon2Hash32 (poseidon2FullTagPreimage sh msg))

theorem poseidon2FullTagPreimage_eq_iff {sh₁ msg₁ sh₂ msg₂ : List UInt8} :
    poseidon2FullTagPreimage sh₁ msg₁ = poseidon2FullTagPreimage sh₂ msg₂ ↔
      sh₁ = sh₂ ∧ msg₁ = msg₂ := by
  constructor
  · intro h
    have hFrames := encodeMultiFrame_injective h
    injection hFrames with _ hTail1
    injection hTail1 with hSh hTail2
    injection hTail2 with hMsg _
    exact ⟨hSh, hMsg⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- **Constructive Full-Key/Full-Message Tag Binding (`poseidon2FullTagPreimage_injective`, `0 Classical`)**:
    Any distinct `(sh₁, msg₁) ≠ (sh₂, msg₂)` producing equal 32-byte `poseidon2TagBytes`
    constructively yields a concrete `HashCollisionWitness poseidon2Hash32`. -/
def poseidon2FullTagPreimage_injective (sh₁ msg₁ sh₂ msg₂ : List UInt8)
    (hNe : (sh₁, msg₁) ≠ (sh₂, msg₂))
    (hEqTag : poseidon2TagBytes sh₁ msg₁ = poseidon2TagBytes sh₂ msg₂) :
    HashCollisionWitness poseidon2Hash32 :=
  { m1 := poseidon2FullTagPreimage sh₁ msg₁
    m2 := poseidon2FullTagPreimage sh₂ msg₂
    ne := fun hPre => by
      obtain ⟨rfl, rfl⟩ := poseidon2FullTagPreimage_eq_iff.mp hPre
      exact hNe rfl
    eq := packWire_injective hEqTag }

/-- Retired 2-share-byte / 1-message-byte / 4-byte-output tag (retained strictly for `#tooth` regression). -/
def retiredTruncatedPrefixTagBytes (sh msg : List UInt8) : ByteArray :=
  let k0 := Goldilocks.ofNat (sh.getD 0 0).toNat
  let k1 := Goldilocks.ofNat (sh.getD 1 0).toNat
  let m0 := Goldilocks.ofNat (msg.getD 0 0).toNat
  let mL := Goldilocks.ofNat msg.length
  let out := (applyME ⟨⟨sbox7 k0, sbox7 k1, sbox7 m0, sbox7 mL⟩,
    ⟨Goldilocks.ofNat 0x51534147, Goldilocks.one, Goldilocks.zero, Goldilocks.zero⟩,
    ⟨Goldilocks.zero, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩⟩).b0
  packWire [UInt8.ofNat (out.x0.val % 256), UInt8.ofNat (out.x1.val % 256),
            UInt8.ofNat (out.x2.val % 256), UInt8.ofNat (out.x3.val % 256)]

/-- **`#tooth` Regression (`tooth_truncated_prefix_tag_collides_ab_ac`)**:
    1. The retired 2-byte/first-byte 4-byte construction collides unconditionally on `"AB"`
       (`[0x41, 0x42]`) vs `"AC"` (`[0x41, 0x43]`) for EVERY key `sh`, and ignores bytes `2..31`
       of a 32-byte key for EVERY message `msg`,
    2. The upgraded 32-byte (`256`-bit) `poseidon2TagBytes` absorbs every byte of `sh` and `msg`
       into distinct canonical sponge preimages (`poseidon2FullTagPreimage_injective`), so any
       tag collision on `"AB"` vs `"AC"` or `key32A` vs `key32B` constructively yields a
       `HashCollisionWitness poseidon2Hash32`. -/
theorem tooth_truncated_prefix_tag_collides_ab_ac :
    let key32A := (List.range 32).map UInt8.ofNat
    let key32B := (List.range 31).map UInt8.ofNat ++ [0xFF]
    let msgAB : List UInt8 := [0x41, 0x42]
    let msgAC : List UInt8 := [0x41, 0x43]
    (∀ sh : List UInt8,
      retiredTruncatedPrefixTagBytes sh msgAB = retiredTruncatedPrefixTagBytes sh msgAC) ∧
    (∀ msg : List UInt8,
      retiredTruncatedPrefixTagBytes key32A msg = retiredTruncatedPrefixTagBytes key32B msg) ∧
    (unpackWire (retiredTruncatedPrefixTagBytes key32A msgAB)).length = 4 ∧
    (unpackWire (poseidon2TagBytes key32A msgAB)).length = 32 ∧
    poseidon2FullTagPreimage key32A msgAB ≠ poseidon2FullTagPreimage key32A msgAC ∧
    poseidon2FullTagPreimage key32A msgAB ≠ poseidon2FullTagPreimage key32B msgAB ∧
    (poseidon2TagBytes key32A msgAB = poseidon2TagBytes key32A msgAC →
      Nonempty (HashCollisionWitness poseidon2Hash32)) ∧
    (poseidon2TagBytes key32A msgAB = poseidon2TagBytes key32B msgAB →
      Nonempty (HashCollisionWitness poseidon2Hash32)) := by
  intro key32A key32B msgAB msgAC
  have hMsgNe : msgAB ≠ msgAC := by decide
  have hKeyNe : key32A ≠ key32B := by decide
  refine ⟨fun _ => rfl, fun _ => rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · unfold poseidon2TagBytes
    rw [unpackWire_packWire]
    exact poseidon2Hash32_length _
  · intro hPre
    exact hMsgNe (poseidon2FullTagPreimage_eq_iff.mp hPre).2
  · intro hPre
    exact hKeyNe (poseidon2FullTagPreimage_eq_iff.mp hPre).1
  · intro hEq
    exact ⟨poseidon2FullTagPreimage_injective key32A msgAB key32A msgAC
      (fun h => hMsgNe (Prod.mk.inj h).2) hEq⟩
  · intro hEq
    exact ⟨poseidon2FullTagPreimage_injective key32A msgAB key32B msgAB
      (fun h => hKeyNe (Prod.mk.inj h).1) hEq⟩

/-- Round-2 wire opening supplied in `FourLayerReq`: carries ONLY `(wireId, xWire, macShare)`.
    The verifier-held global MAC scalar `verifierBginAlpha` and per-wire offset `storedKeyOffset`
    live exclusively inside machine state and are never read from the request. -/
structure Round2WireOpening where
  wireId : Nat
  xWire : Tower128
  macShare : Tower128
  deriving DecidableEq

/-- Machine-held validator authentication keys `(partyIdx, authKey32)` for `§4` quorum certificates. -/
structure QuorumCertConfig where
  validatorAuthKeys : List (Nat × List UInt8)
  deriving DecidableEq

/-- Unified end-to-end signing request traversing all 4 layers: supplies transaction intent,
    epoch, quorum, `§4`-authenticated `(validator, ackTag)` quorum certificate, Round-1 openings,
    and Round-2 `(wireId, xWire, macShare)` wire openings. -/
structure FourLayerReq (n : Nat) where
  tx : MirTxIntent
  reqEpoch : Nat
  quorum : List (Fin n)
  quorumCert : List (Fin n × List UInt8)
  round1Openings : List Round1Opening
  round2Wires : List Round2WireOpening
  deriving DecidableEq

/-- Unified end-to-end output emitted upon unanimous 4-layer authorization and signature assembly. -/
structure FourLayerOut where
  envelope : ApprovedIntentEnvelope
  committedEpoch : Nat
  sigBytes : ByteArray
  deriving DecidableEq

/-- Domain separation tag `"QSAG.MIR.QUORUM.ACK.V1"` for validator quorum-approval MAC tags. -/
def quorumAckDomainTag : List UInt8 :=
  [0x51, 0x53, 0x41, 0x47, 0x2E, 0x4D, 0x49, 0x52,
   0x2E, 0x51, 0x55, 0x4F, 0x52, 0x55, 0x4D, 0x2E,
   0x41, 0x43, 0x4B, 0x2E, 0x56, 0x31]

def lookupValidatorAuthKey (keys : List (Nat × List UInt8)) (partyIdx : Nat) : Option (List UInt8) :=
  match keys.find? (fun kv => kv.1 == partyIdx) with
  | some (_, k) => some k
  | none => none

def computeValidatorAckTag (authKey : List UInt8) (partyIdx epoch : Nat) (msgBytes : List UInt8) : List UInt8 :=
  poseidon2Hash32 (encodeMultiFrame [quorumAckDomainTag, authKey, leb128 partyIdx, leb128 epoch, msgBytes])

def verifyValidatorAck {n : Nat} (cfg : QuorumCertConfig)
    (p : Fin n) (epoch : Nat) (msgBytes : List UInt8) (ackTag : List UInt8) : Bool :=
  match lookupValidatorAuthKey cfg.validatorAuthKeys p.val with
  | none => false
  | some authKey =>
    decide (authKey.length = 32) &&
      decide (ackTag = computeValidatorAckTag authKey p.val epoch msgBytes)

theorem verifyValidatorAck_of_eq {n : Nat} {cfg : QuorumCertConfig}
    {p : Fin n} {epoch : Nat} {msgBytes ackTag authKey : List UInt8}
    (hLookup : lookupValidatorAuthKey cfg.validatorAuthKeys p.val = some authKey)
    (hLen : authKey.length = 32)
    (hTag : ackTag = computeValidatorAckTag authKey p.val epoch msgBytes) :
    verifyValidatorAck cfg p epoch msgBytes ackTag = true := by
  unfold verifyValidatorAck
  rw [hLookup]
  simp [decide_eq_true hLen, decide_eq_true hTag]

/-- Invoke `§4`'s `beltCertAuthenticated` against `cfg.validatorAuthKeys` while binding
    `beltReq.signers = req.quorum`. -/
def verifyFourLayerQuorumCert {n : Nat} (cfg : QuorumCertConfig) (q : Nat)
    (pkDigest msgBytes : List UInt8) (req : FourLayerReq n) : Bool :=
  let beltReq : BeltLatchCommitReq n :=
    { pkDigest := pkDigest
      reqEpoch := req.reqEpoch
      msgDigest := msgBytes
      freshSig := ByteArray.empty
      quorumCert := req.quorumCert }
  decide (beltReq.signers = req.quorum) &&
    beltCertAuthenticated (verifyValidatorAck cfg) q beltReq

theorem verifyFourLayerQuorumCert_implies_nodup_and_len {n : Nat}
    {cfg : QuorumCertConfig} {q : Nat} {pkDigest msgBytes : List UInt8} {req : FourLayerReq n}
    (h : verifyFourLayerQuorumCert cfg q pkDigest msgBytes req = true) :
    req.quorum.Nodup ∧ q ≤ req.quorum.length := by
  unfold verifyFourLayerQuorumCert beltCertAuthenticated at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨hSigners, ⟨_, hNd⟩, hLen⟩
  have hLenSigners :
      (BeltLatchCommitReq.signers
        ⟨pkDigest, req.reqEpoch, msgBytes, ByteArray.empty, req.quorumCert⟩).length =
      req.quorumCert.length :=
    List.length_map _
  rw [hSigners] at hNd hLenSigners
  exact ⟨hNd, hLenSigners ▸ hLen⟩

theorem verifyFourLayerQuorumCert_eq_true {n : Nat}
    {cfg : QuorumCertConfig} {q : Nat} {pkDigest msgBytes : List UInt8} {req : FourLayerReq n}
    (hSigners : req.quorumCert.map Prod.fst = req.quorum)
    (hNd : req.quorum.Nodup)
    (hLen : q ≤ req.quorumCert.length)
    (hAll : ∀ e ∈ req.quorumCert,
      ∃ authKey : List UInt8,
        lookupValidatorAuthKey cfg.validatorAuthKeys e.1.val = some authKey ∧
        authKey.length = 32 ∧
        e.2 = computeValidatorAckTag authKey e.1.val req.reqEpoch msgBytes) :
    verifyFourLayerQuorumCert cfg q pkDigest msgBytes req = true := by
  unfold verifyFourLayerQuorumCert beltCertAuthenticated
  dsimp only
  have hBs :
      BeltLatchCommitReq.signers
        ⟨pkDigest, req.reqEpoch, msgBytes, ByteArray.empty, req.quorumCert⟩ = req.quorum :=
    hSigners
  have hAllB :
      req.quorumCert.all (fun e => verifyValidatorAck cfg e.1 req.reqEpoch msgBytes e.2) = true := by
    rw [List.all_eq_true]
    intro e he
    obtain ⟨authKey, hLk, hKL, hTg⟩ := hAll e he
    exact verifyValidatorAck_of_eq hLk hKL hTg
  rw [decide_eq_true hBs, hAllB, decide_eq_true (hBs.symm ▸ hNd), decide_eq_true hLen]
  rfl

def lookupBginKeyOffset (offsets : List (Nat × Tower128)) (wireId : Nat) : Option Tower128 :=
  match offsets.find? (fun kv => kv.1 == wireId) with
  | some (_, k) => some k
  | none => none

/-- Verify a single Round-2 wire opening against machine-held `(verifierAlpha, verifierKeyOffsets)`. -/
def verifySessionBginWire (verifierAlpha : Tower128) (verifierKeyOffsets : List (Nat × Tower128))
    (w : Round2WireOpening) : Bool :=
  match lookupBginKeyOffset verifierKeyOffsets w.wireId with
  | none => false
  | some storedKeyOffset =>
    bginRelationHolds
      { xWire := w.xWire
        macShare := w.macShare
        keyOffset := storedKeyOffset
        alpha := verifierAlpha }

/-- Verify all Round-2 wire openings against machine-held non-zero `verifierAlpha` and
    `verifierKeyOffsets`, requiring every registered wire in `verifierKeyOffsets` to be opened. -/
def verifySessionBginBatch (verifierAlpha : Tower128) (verifierKeyOffsets : List (Nat × Tower128))
    (wires : List Round2WireOpening) : Bool :=
  decide (verifierAlpha ≠ towerZero 7) &&
  !verifierKeyOffsets.isEmpty &&
  !wires.isEmpty &&
  decide (wires.map Round2WireOpening.wireId).Nodup &&
  verifierKeyOffsets.all (fun wk => wires.any (fun w => w.wireId == wk.1)) &&
  wires.all (verifySessionBginWire verifierAlpha verifierKeyOffsets)

/-- Verify Round-1 openings against machine-held `activeSessionTag` and the active quorum batch
    `storedRound1Commits.take quorum.length`, requiring every member of `quorum` to have a
    matching stored `(partyId, committedB0)` and valid opening. -/
def verifySessionRound1Openings {n : Nat} (activeSessionTag : Goldilocks)
    (storedRound1Commits : List (Nat × Lane4)) (quorum : List (Fin n))
    (openings : List Round1Opening) : Bool :=
  let activeBatch := storedRound1Commits.take quorum.length
  (activeBatch.length == quorum.length) &&
  !openings.isEmpty &&
  decide (openings.map (fun op => op.partyId.val)).Nodup &&
  quorum.all (fun p => openings.any (fun op => op.partyId.val == p.val)) &&
  openings.all (fun op =>
    decide (op.sessionTag = activeSessionTag) &&
    decide ((op.partyId.val, op.committedB0) ∈ activeBatch) &&
    verifyRound1Opening op)

theorem verifySessionRound1Openings_eq_true {n : Nat}
    {activeSessionTag : Goldilocks}
    {storedRound1Commits : List (Nat × Lane4)}
    {quorum : List (Fin n)}
    {openings : List Round1Opening}
    (hBatchLen : (storedRound1Commits.take quorum.length).length = quorum.length)
    (hNonEmpty : (!openings.isEmpty) = true)
    (hNd : (openings.map (fun op => op.partyId.val)).Nodup)
    (hCover : quorum.all (fun p => openings.any (fun op => op.partyId.val == p.val)) = true)
    (hAll : ∀ op ∈ openings,
      op.sessionTag = activeSessionTag ∧
      (op.partyId.val, op.committedB0) ∈ storedRound1Commits.take quorum.length ∧
      op.committedB0 =
        computeRound1CommitB0 op.nonceLimb op.maskLimb op.sessionTag op.partyId op.blind) :
    verifySessionRound1Openings activeSessionTag storedRound1Commits quorum openings = true := by
  unfold verifySessionRound1Openings
  dsimp only
  have hBL : ((storedRound1Commits.take quorum.length).length == quorum.length) = true :=
    beq_iff_eq.mpr hBatchLen
  have hAllB :
      openings.all (fun op =>
        decide (op.sessionTag = activeSessionTag) &&
        decide ((op.partyId.val, op.committedB0) ∈ storedRound1Commits.take quorum.length) &&
        verifyRound1Opening op) = true := by
    rw [List.all_eq_true]
    intro op hop
    obtain ⟨hTag, hMem, hCom⟩ := hAll op hop
    rw [decide_eq_true hTag, decide_eq_true hMem, verifyRound1Opening_of_eq hCom]
    rfl
  rw [hBL, hNonEmpty, decide_eq_true hNd, hCover, hAllB]
  rfl

/-- Consume the active quorum batch from `storedRound1Commits` upon cut release so opened
    Round-1 commitments cannot be reused in subsequent sessions. -/
def consumeRound1Commits {n : Nat} (storedRound1Commits : List (Nat × Lane4))
    (quorum : List (Fin n)) : List (Nat × Lane4) :=
  storedRound1Commits.drop quorum.length

/-- Session-bound pre-cut transcript verifier authenticating Round-1 openings against
    `activeSessionTag` + `storedRound1Commits` (covering `quorum`) AND Round-2 wire MACs against
    machine-held `verifierBginAlpha` + `verifierBginKeyOffsets`. -/
def verifyPreCutTranscript {n : Nat}
    (activeSessionTag : Goldilocks)
    (storedRound1Commits : List (Nat × Lane4))
    (verifierBginAlpha : Tower128)
    (verifierBginKeyOffsets : List (Nat × Tower128))
    (quorum : List (Fin n))
    (openings : List Round1Opening)
    (round2Wires : List Round2WireOpening) : Bool :=
  verifySessionRound1Openings activeSessionTag storedRound1Commits quorum openings &&
  verifySessionBginBatch verifierBginAlpha verifierBginKeyOffsets round2Wires

/-- Run the historical pinned `.rlib` fixture `qsag_asm_ct_eq_32_x86_64` slice from `x86ExtractedSlices`
    on address `ptrPinned` (`0x100` or `0x140`) vs `0x200` with candidate `cand` loaded at `0x200`. -/
def execElfCtEq32 (m : UInt64 → UInt8) (ptrPinned : UInt64) (cand : List UInt8) : Bool :=
  if cand.length != 32 then false
  else
    match (findSliceByNameBytes x86ExtractedSlices ctEq32X86Name).bind
            (fun sl => decodeX86Stream sl.code) with
    | none => false
    | some prog =>
      let mCall := writeBytesWindow m 0x200 cand
      let out := (runX86 prog 20 (mkX86MemCall ptrPinned 0x200 0 mCall)).1
      out.halted && (out.gpr.get 0 == 1)

/-- Run the historical pinned `.rlib` fixture `qsag_asm_ct_memzero_x86_64` slice (`132` instructions with
    `mfence; ret`) to physically wipe the 32-byte key-share memory region `[0x180, 0x1A0)`. -/
def execElfMemzeroShare32 (m : UInt64 → UInt8) : UInt64 → UInt8 :=
  match (findSliceByNameBytes x86ExtractedSlices ctMemzeroX86Name).bind
          (fun sl => decodeX86Stream sl.code) with
  | none => fun _ => 0
  | some prog =>
    (runX86 prog 132 (mkX86MemCall 0x180 32 0 m)).1.mem

private theorem execElfCtEq32_spec {m : UInt64 → UInt8} {pinned cand : List UInt8}
    {base : Nat}
    (hPinnedLen : pinned.length = 32)
    (hBaseBound : base + 32 ≤ 0x180)
    (hMemPinned : ∀ i : Nat, i < 32 → m (UInt64.ofNat base + UInt64.ofNat i) = pinned.getD i 0) :
    execElfCtEq32 m (UInt64.ofNat base) cand = decide (cand = pinned) := by
  unfold execElfCtEq32
  cases hLenNe : (cand.length != 32)
  · have hCandLen : cand.length = 32 := by
      cases hEq : (cand.length == 32)
      · rw [bne, hEq] at hLenNe; cases hLenNe
      · exact Nat.eq_of_beq_eq_true hEq
    simp only [Bool.false_eq_true, ↓reduceIte]
    obtain ⟨sl, prog, hf, hd, hSpec⟩ := ct_eq_32_x86_64_mc_refines
    rw [hf]
    dsimp only [Option.bind]
    rw [hd]
    dsimp only
    let mCall := writeBytesWindow m 0x200 cand
    obtain ⟨hHalt, hRax, _⟩ :=
      hSpec (mkX86MemCall (UInt64.ofNat base) 0x200 0 mCall) 20 rfl rfl (Nat.le_refl 20)
    have hG7 : (mkX86MemCall (UInt64.ofNat base) 0x200 0 mCall).gpr.get 7 = UInt64.ofNat base := rfl
    have hG6 : (mkX86MemCall (UInt64.ofNat base) 0x200 0 mCall).gpr.get 6 = 0x200 := rfl
    have hMemS : (mkX86MemCall (UInt64.ofNat base) 0x200 0 mCall).mem = mCall := rfl
    rw [hG7, hG6, hMemS] at hRax
    have h200 : (0x200 : UInt64) = UInt64.ofNat 0x200 := rfl
    have hWindowIff :
        (∀ i : Nat, i < 32 →
          mCall (UInt64.ofNat base + UInt64.ofNat i) = mCall ((0x200 : UInt64) + UInt64.ofNat i)) ↔
        cand = pinned := by
      have hEqGetD := list_eq_iff_getD_eq (hCandLen.trans hPinnedLen.symm)
      rw [hCandLen] at hEqGetD
      refine Iff.trans ?_ hEqGetD.symm
      constructor
      · intro hAll i hi
        have hRead := hAll i hi
        have hL : mCall (UInt64.ofNat base + UInt64.ofNat i) = pinned.getD i 0 := by
          dsimp only [mCall]
          have hToNat := addr_offset_toNat (base := base) (i := i) (by omega)
          rw [writeBytesWindow_miss (by rw [hToNat]; omega), hMemPinned i hi]
        have hR : mCall (UInt64.ofNat 0x200 + UInt64.ofNat i) = cand.getD i 0 :=
          writeBytesWindow_hit (hCandLen ▸ hi) (by omega)
        rw [h200] at hRead
        exact (hL.symm.trans (hRead.trans hR)).symm
      · intro hAll i hi
        have hL : mCall (UInt64.ofNat base + UInt64.ofNat i) = pinned.getD i 0 := by
          dsimp only [mCall]
          have hToNat := addr_offset_toNat (base := base) (i := i) (by omega)
          rw [writeBytesWindow_miss (by rw [hToNat]; omega), hMemPinned i hi]
        have hR : mCall (UInt64.ofNat 0x200 + UInt64.ofNat i) = cand.getD i 0 :=
          writeBytesWindow_hit (hCandLen ▸ hi) (by omega)
        rw [h200, hL, hR]
        exact (hAll i hi).symm
    rw [hHalt, Bool.true_and, hRax]
    if hEq : cand = pinned then
      rw [decide_eq_true hEq, ite_eq_left (hWindowIff.mpr hEq)]
      rfl
    else
      rw [decide_eq_false hEq, ite_eq_right (fun h => hEq (hWindowIff.mp h))]
      rfl
  · have hNe : cand ≠ pinned := by
      intro hEq
      subst hEq
      rw [hPinnedLen] at hLenNe
      cases hLenNe
    simp [decide_eq_false hNe]

private theorem execElfMemzeroShare32_spec (m : UInt64 → UInt8) :
    (∀ i : Nat, i < 32 → execElfMemzeroShare32 m (UInt64.ofNat 0x180 + UInt64.ofNat i) = 0) ∧
    (∀ a : UInt64, a.toNat < 0x180 → execElfMemzeroShare32 m a = m a) := by
  unfold execElfMemzeroShare32
  obtain ⟨sl, prog, hf, hd, hSpec⟩ := ct_memzero_x86_64_mc_refines
  rw [hf]
  dsimp only [Option.bind]
  rw [hd]
  dsimp only
  obtain ⟨_, hZero, hPres⟩ :=
    hSpec (mkX86MemCall 0x180 32 0 m) 132 rfl rfl
      (show 0 < 32 by decide) (show 4 * 32 + 4 ≤ 132 by decide)
  have hG7 : (mkX86MemCall 0x180 32 0 m).gpr.get 7 = UInt64.ofNat 0x180 := rfl
  have hG6 : ((mkX86MemCall 0x180 32 0 m).gpr.get 6).toNat = 32 := rfl
  refine ⟨fun i hi => by have hz := hZero i hi; rwa [hG7] at hz, fun a ha => hPres a ?_⟩
  intro i hi hEq
  rw [hG6] at hi
  have hToNat := congrArg UInt64.toNat hEq
  rw [hG7, addr_offset_toNat (base := 0x180) (i := i) (by omega)] at hToNat
  omega

/-- **Layer 1 State (`Layer1ElfState`)**:
    Holds `X86State` flat memory storing the 32-byte pinned policy digest (`[0x100, 0x120)`),
    32-byte pinned authority digest (`[0x140, 0x160)`), and 32-byte custodian key share
    (`[0x180, 0x1A0)`), paired with fixed-width `UInt64` velocity/nonce counters, `MirBeltLatchState`,
    sticky quarantine flags, and machine-held session evidence (`activeSessionTag`,
    `storedRound1Commits`, `verifierBginAlpha`, `verifierBginKeyOffsets`, `quorumCertConfig`). -/
structure Layer1ElfState where
  mem : UInt64 → UInt8
  windowId : UInt64
  velocityWindowCap : UInt64
  accumulatedSpend : UInt64
  burnedNonces : List UInt64
  allowedRecipients : List (List UInt8)
  perTxCap : UInt64
  belt : MirBeltLatchState
  cutPoisoned : Bool
  sharePresent : Bool
  activeSessionTag : Goldilocks
  storedRound1Commits : List (Nat × Lane4)
  verifierBginAlpha : Tower128
  verifierBginKeyOffsets : List (Nat × Tower128)
  quorumCertConfig : QuorumCertConfig

/-- **Layer 2 State (`Layer2MirState`)**:
    Concrete fixed-width `UInt64` `MirPolicyGuardState` + `MirBeltLatchState` + sticky
    `MirRssCutSession` + machine-held session/MAC/quorum-certificate state. -/
structure Layer2MirState where
  policy : MirPolicyGuardState
  belt : MirBeltLatchState
  cut : MirRssCutSession
  shareBytes : Option (List UInt8)
  activeSessionTag : Goldilocks
  storedRound1Commits : List (Nat × Lane4)
  verifierBginAlpha : Tower128
  verifierBginKeyOffsets : List (Nat × Tower128)
  quorumCertConfig : QuorumCertConfig
  deriving DecidableEq

/-- **Layer 3 State (`Layer3ProtocolState`)**:
    Protocol-level `CustodySuiteFull.StatefulPolicyGuard` + `InteractiveUcEngine.RealClusterState`
    holding honest secret shares (`Nat → Option (List UInt8)`) and machine-held session evidence. -/
structure Layer3ProtocolState (PK : Type) where
  policy : StatefulPolicyGuard
  cluster : RealClusterState PK (List UInt8)
  activeSessionTag : Goldilocks
  storedRound1Commits : List (Nat × Lane4)
  verifierBginAlpha : Tower128
  verifierBginKeyOffsets : List (Nat × Tower128)
  quorumCertConfig : QuorumCertConfig

/-- **Layer 4 State (`Layer4IdealState`)**:
    Signing-share-free target authorization state (`StatefulPolicyGuard` + `IdealClusterState PK`
    + public/verifier session evidence; contains no signing secret shares, while `idealSignOracle`
    is supplied as an external parameter in `layer4IdealTsigMachine`). -/
structure Layer4IdealState (PK : Type) where
  policy : StatefulPolicyGuard
  ideal : IdealClusterState PK
  activeSessionTag : Goldilocks
  storedRound1Commits : List (Nat × Lane4)
  verifierBginAlpha : Tower128
  verifierBginKeyOffsets : List (Nat × Tower128)
  quorumCertConfig : QuorumCertConfig

/-- **Layer 1 Machine (`layer1CompiledElfMachine`)**:
    Executes decoded `.rlib` `qsag_asm_ct_eq_32_x86_64` (`execElfCtEq32`) for both 32-byte digest
    pins, enforces `UInt64` velocity/nonce + `§4`-authenticated `q`-quorum certificate +
    session-bound Round-1 and fixed-key Round-2 pre-cut barrier against machine-held commitments and `BGIN19`
    keys, and executes decoded `.rlib` `qsag_asm_ct_memzero_x86_64` (`execElfMemzeroShare32`) to
    zeroize `[0x180, 0x1A0)` upon any active Round-1/Round-2 fault. -/
@[expose]
def layer1CompiledElfMachine {n : Nat} (q : Nat) (pkDigest : List UInt8)
    (signFromShareMem : (UInt64 → UInt8) → List UInt8 → ByteArray) :
    PartyMachine Layer1ElfState (FourLayerReq n) FourLayerOut :=
  PartyMachine.ofOutcome fun s req =>
    if s.cutPoisoned || s.belt.poisoned || !s.sharePresent then
      .err { s with mem := execElfMemzeroShare32 s.mem,
                    belt := { s.belt with poisoned := true },
                    cutPoisoned := true, sharePresent := false } ()
    else if req.tx.windowId != s.windowId then .err s ()
    else if !execElfCtEq32 s.mem (UInt64.ofNat 0x100) req.tx.policyDigest then .err s ()
    else if !execElfCtEq32 s.mem (UInt64.ofNat 0x140) req.tx.authorityDigest then .err s ()
    else if ¬ (req.tx.recipient ∈ s.allowedRecipients) then .err s ()
    else if ¬ (req.tx.amountUnits.toNat ≤ s.perTxCap.toNat) then .err s ()
    else if ¬ (req.tx.amountUnits.toNat ≤ (s.velocityWindowCap - s.accumulatedSpend).toNat) then .err s ()
    else if u64MemBool req.tx.nonce s.burnedNonces then .err s ()
    else
      let intent := req.tx.toTransactionIntent
      let msgBytes := encodeTransactionIntent intent
      if !verifyFourLayerQuorumCert s.quorumCertConfig q pkDigest msgBytes req then .err s ()
      else if !(decide (pkDigest = s.belt.enrolledPkDigest) && (req.reqEpoch == s.belt.nextEpoch)) then
        .err s ()
      else if !verifyPreCutTranscript s.activeSessionTag s.storedRound1Commits
          s.verifierBginAlpha s.verifierBginKeyOffsets req.quorum
          req.round1Openings req.round2Wires then
        -- Active Round-1 / Round-2 consistency fault: run compiled `ct_memzero` on `[0x180, 0x1A0)`
        -- and latch sticky quarantine BEFORE any Round-3 cut share can be computed!
        .err { s with mem := execElfMemzeroShare32 s.mem,
                      belt := { s.belt with poisoned := true },
                      cutPoisoned := true, sharePresent := false } ()
      else
        let sigBytes := signFromShareMem s.mem msgBytes
        let env : ApprovedIntentEnvelope := { intent := intent, canonicalBytes := msgBytes }
        let belt' : MirBeltLatchState :=
          { s.belt with
            nextEpoch := req.reqEpoch + 1
            latchedRecord := some (req.reqEpoch, msgBytes, sigBytes) }
        let s' : Layer1ElfState :=
          { s with
            accumulatedSpend := s.accumulatedSpend + req.tx.amountUnits
            burnedNonces := req.tx.nonce :: s.burnedNonces
            belt := belt'
            activeSessionTag := Goldilocks.add s.activeSessionTag Goldilocks.one
            storedRound1Commits := consumeRound1Commits s.storedRound1Commits req.quorum }
        .ok s' { envelope := env, committedEpoch := req.reqEpoch, sigBytes := sigBytes }

/-- **Layer 2 Machine (`layer2MirGuardedMachine`)**:
    Composes concrete fixed-width `UInt64` `mirPolicyStep`, `§4`-authenticated `q`-quorum
    `MirBeltLatchState`, sticky `MirRssCutSession`, and session-bound pre-cut verification against
    machine-held commitments and `BGIN19` MAC keys. -/
@[expose]
def layer2MirGuardedMachine {n : Nat} (q : Nat) (pkDigest : List UInt8)
    (signFromShare : List UInt8 → List UInt8 → ByteArray) :
    PartyMachine Layer2MirState (FourLayerReq n) FourLayerOut :=
  PartyMachine.ofOutcome fun s req =>
    if s.cut.poisoned || s.belt.poisoned || s.shareBytes.isNone then
      .err { s with belt := { s.belt with poisoned := true },
                    cut := mirRssCutPoison s.cut,
                    shareBytes := none } ()
    else
      match mirPolicyStep s.policy req.tx with
      | none => .err s ()
      | some (pol', env) =>
        if !verifyFourLayerQuorumCert s.quorumCertConfig q pkDigest env.canonicalBytes req then
          .err s ()
        else if !(decide (pkDigest = s.belt.enrolledPkDigest) && (req.reqEpoch == s.belt.nextEpoch)) then
          .err s ()
        else if !verifyPreCutTranscript s.activeSessionTag s.storedRound1Commits
            s.verifierBginAlpha s.verifierBginKeyOffsets req.quorum
            req.round1Openings req.round2Wires then
          .err { s with belt := { s.belt with poisoned := true },
                        cut := mirRssCutPoison s.cut,
                        shareBytes := none } ()
        else
          match s.shareBytes with
          | none => .err s ()
          | some sh =>
            let sigBytes := signFromShare sh env.canonicalBytes
            let belt' : MirBeltLatchState :=
              { s.belt with
                nextEpoch := req.reqEpoch + 1
                latchedRecord := some (req.reqEpoch, env.canonicalBytes, sigBytes) }
            let cut' : MirRssCutSession :=
              MirRssCutSession.round1Committed s.cut.sessionId s.cut.maskCommitment
            .ok { s with
                  policy := pol'
                  belt := belt'
                  cut := cut'
                  shareBytes := some sh
                  activeSessionTag := Goldilocks.add s.activeSessionTag Goldilocks.one
                  storedRound1Commits := consumeRound1Commits s.storedRound1Commits req.quorum }
                { envelope := env, committedEpoch := req.reqEpoch, sigBytes := sigBytes }

/-- **Layer 3 Machine (`layer3InteractiveProtocolMachine`)**:
    Multi-party 3-round interactive threshold signing cluster (`StatefulPolicyGuard` +
    `RealClusterState PK (List UInt8)` with `§4`-authenticated quorum certificate,
    `validThresholdApproval`, `WalLatchState`, session-bound pre-cut consistency barrier,
    `poisonRealCluster` on fault, and Round-3 threshold signature assembly). -/
@[expose]
def layer3InteractiveProtocolMachine {PK : Type} {n : Nat}
    (corrupt : List (Fin n)) (pkDigestOf : PK → List UInt8)
    (assembleThresholdSig : (Nat → Option (List UInt8)) → List UInt8 → ByteArray) :
    PartyMachine (Layer3ProtocolState PK) (FourLayerReq n) FourLayerOut :=
  PartyMachine.ofOutcome fun s req =>
    if s.cluster.honestWal.poisoned then
      .err { s with cluster := poisonRealCluster s.cluster } ()
    else
      match policyGuardStep s.policy req.tx.toTransactionIntent with
      | .rejected _ _ => .err s ()
      | .accepted pol' env =>
        let pkDig := pkDigestOf s.cluster.tsig.pk
        let honApprovers := (req.quorum.filter (fun p => !finMemBool p corrupt)).map Fin.val
        if !(verifyFourLayerQuorumCert s.quorumCertConfig s.cluster.tsig.threshold pkDig env.canonicalBytes req &&
             validThresholdApproval s.cluster.tsig honApprovers) then
          .err s ()
        else if !(decide (pkDig = s.cluster.honestWal.enrolledPkDigest) &&
                  (req.reqEpoch == s.cluster.honestWal.nextEpoch)) then
          .err s ()
        else if !verifyPreCutTranscript s.activeSessionTag s.storedRound1Commits
            s.verifierBginAlpha s.verifierBginKeyOffsets req.quorum
            req.round1Openings req.round2Wires then
          .err { s with cluster := poisonRealCluster s.cluster } ()
        else
          let sigBytes := assembleThresholdSig s.cluster.honestShares env.canonicalBytes
          let wal' : WalLatchState :=
            { s.cluster.honestWal with
              nextEpoch := req.reqEpoch + 1
              latchedRecord := some (req.reqEpoch, env.canonicalBytes, sigBytes) }
          let tsig' :=
            { s.cluster.tsig with approvedMsgs := env.canonicalBytes :: s.cluster.tsig.approvedMsgs }
          let cl' : RealClusterState PK (List UInt8) :=
            { s.cluster with
              tsig := tsig'
              honestWal := wal'
              maskSessionCursor := s.cluster.maskSessionCursor + 1 }
          .ok { s with
                policy := pol'
                cluster := cl'
                activeSessionTag := Goldilocks.add s.activeSessionTag Goldilocks.one
                storedRound1Commits := consumeRound1Commits s.storedRound1Commits req.quorum }
              { envelope := env, committedEpoch := req.reqEpoch, sigBytes := sigBytes }

/-- **Layer 4 Machine (`layer4IdealTsigMachine`)**:
    Target authorization and epoch-latch machine over share-free `Layer4IdealState`, invoking the
    externally supplied `idealSignOracle` ONLY when authoritative `StatefulPolicyGuard`,
    `§4`-authenticated quorum certificate, `validThresholdApproval`, `WalLatchState`, and the
    session-bound pre-cut barrier all succeed. -/
@[expose]
def layer4IdealTsigMachine {PK : Type} {n : Nat}
    (corrupt : List (Fin n)) (pkDigestOf : PK → List UInt8)
    (idealSignOracle : List UInt8 → ByteArray) :
    PartyMachine (Layer4IdealState PK) (FourLayerReq n) FourLayerOut :=
  PartyMachine.ofOutcome fun s req =>
    if s.ideal.honestWal.poisoned then
      .err { s with ideal := poisonIdealCluster s.ideal } ()
    else
      match policyGuardStep s.policy req.tx.toTransactionIntent with
      | .rejected _ _ => .err s ()
      | .accepted pol' env =>
        let pkDig := pkDigestOf s.ideal.tsig.pk
        let honApprovers := (req.quorum.filter (fun p => !finMemBool p corrupt)).map Fin.val
        if !(verifyFourLayerQuorumCert s.quorumCertConfig s.ideal.tsig.threshold pkDig env.canonicalBytes req &&
             validThresholdApproval s.ideal.tsig honApprovers) then
          .err s ()
        else if !(decide (pkDig = s.ideal.honestWal.enrolledPkDigest) &&
                  (req.reqEpoch == s.ideal.honestWal.nextEpoch)) then
          .err s ()
        else if !verifyPreCutTranscript s.activeSessionTag s.storedRound1Commits
            s.verifierBginAlpha s.verifierBginKeyOffsets req.quorum
            req.round1Openings req.round2Wires then
          .err { s with ideal := poisonIdealCluster s.ideal } ()
        else
          let sigBytes := idealSignOracle env.canonicalBytes
          let wal' : WalLatchState :=
            { s.ideal.honestWal with
              nextEpoch := req.reqEpoch + 1
              latchedRecord := some (req.reqEpoch, env.canonicalBytes, sigBytes) }
          let tsig' :=
            { s.ideal.tsig with approvedMsgs := env.canonicalBytes :: s.ideal.tsig.approvedMsgs }
          let icl' : IdealClusterState PK :=
            { s.ideal with
              tsig := tsig'
              honestWal := wal'
              maskSessionCursor := s.ideal.maskSessionCursor + 1 }
          .ok { s with
                policy := pol'
                ideal := icl'
                activeSessionTag := Goldilocks.add s.activeSessionTag Goldilocks.one
                storedRound1Commits := consumeRound1Commits s.storedRound1Commits req.quorum }
              { envelope := env, committedEpoch := req.reqEpoch, sigBytes := sigBytes }

/-- Read 32 bytes `[0x180, 0x1A0)` from `X86State` memory as a canonical `List UInt8`. -/
def readShareMem32 (m : UInt64 → UInt8) : List UInt8 :=
  (List.range 32).map (fun i => m (UInt64.ofNat 0x180 + UInt64.ofNat i))

private theorem readShareMem32_write (m : UInt64 → UInt8) (sh : List UInt8) (hLen : sh.length = 32) :
    readShareMem32 (writeBytesWindow m 0x180 sh) = sh := by
  apply (list_eq_iff_getD_eq (by simp [readShareMem32, hLen])).mpr
  intro i hi
  simp only [readShareMem32, List.length_map, List.length_range] at hi
  have hGet :
      ((List.range 32).map (fun j => writeBytesWindow m 0x180 sh (UInt64.ofNat 0x180 + UInt64.ofNat j))).getD i 0 =
        writeBytesWindow m 0x180 sh (UInt64.ofNat 0x180 + UInt64.ofNat i) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
    rfl
  unfold readShareMem32
  rw [hGet, writeBytesWindow_hit (hLen ▸ hi) (by omega)]

private def Layer12SessionEq (s1 : Layer1ElfState) (s2 : Layer2MirState) : Prop :=
  s1.activeSessionTag = s2.activeSessionTag ∧
  s1.storedRound1Commits = s2.storedRound1Commits ∧
  s1.verifierBginAlpha = s2.verifierBginAlpha ∧
  s1.verifierBginKeyOffsets = s2.verifierBginKeyOffsets ∧
  s1.quorumCertConfig = s2.quorumCertConfig

private def Layer23SessionEq {PK : Type} (s2 : Layer2MirState) (s3 : Layer3ProtocolState PK) : Prop :=
  s2.activeSessionTag = s3.activeSessionTag ∧
  s2.storedRound1Commits = s3.storedRound1Commits ∧
  s2.verifierBginAlpha = s3.verifierBginAlpha ∧
  s2.verifierBginKeyOffsets = s3.verifierBginKeyOffsets ∧
  s2.quorumCertConfig = s3.quorumCertConfig

private def Layer34SessionEq {PK : Type} (s3 : Layer3ProtocolState PK) (s4 : Layer4IdealState PK) : Prop :=
  s3.activeSessionTag = s4.activeSessionTag ∧
  s3.storedRound1Commits = s4.storedRound1Commits ∧
  s3.verifierBginAlpha = s4.verifierBginAlpha ∧
  s3.verifierBginKeyOffsets = s4.verifierBginKeyOffsets ∧
  s3.quorumCertConfig = s4.quorumCertConfig

/-- **Link 1 (`sim_layer1_to_layer2`)**:
    `ForwardSim` from `layer1CompiledElfMachine` (executing decoded `.rlib` x86-64 `ct_eq_32` and
    `ct_memzero` slices) to `layer2MirGuardedMachine`, proved via `ct_eq_32_x86_64_mc_refines`
    and `ct_memzero_x86_64_mc_refines`. -/
def sim_layer1_to_layer2 {n : Nat} (q : Nat) (pkDigest : List UInt8)
    (signFromShare : List UInt8 → List UInt8 → ByteArray) :
    ForwardSim
      (layer1CompiledElfMachine (n := n) q pkDigest (fun m msg => signFromShare (readShareMem32 m) msg))
      (layer2MirGuardedMachine (n := n) q pkDigest signFromShare) where
  Rel s1 s2 :=
    s2.policy.pinnedPolicyDigest.length = 32 ∧
    s2.policy.pinnedAuthorityDigest.length = 32 ∧
    (∀ i : Nat, i < 32 →
      s1.mem (UInt64.ofNat 0x100 + UInt64.ofNat i) = s2.policy.pinnedPolicyDigest.getD i 0) ∧
    (∀ i : Nat, i < 32 →
      s1.mem (UInt64.ofNat 0x140 + UInt64.ofNat i) = s2.policy.pinnedAuthorityDigest.getD i 0) ∧
    s1.windowId = s2.policy.windowId ∧
    s1.velocityWindowCap = s2.policy.velocityWindowCap ∧
    s1.accumulatedSpend = s2.policy.accumulatedSpend ∧
    s1.burnedNonces = s2.policy.burnedNonces ∧
    s1.allowedRecipients = s2.policy.allowedRecipients ∧
    s1.perTxCap = s2.policy.perTxCap ∧
    s1.belt = s2.belt ∧
    s1.cutPoisoned = s2.cut.poisoned ∧
    s1.sharePresent = s2.shareBytes.isSome ∧
    Layer12SessionEq s1 s2 ∧
    (s1.cutPoisoned = false → s1.belt.poisoned = false → s1.sharePresent = true →
      s2.shareBytes = some (readShareMem32 s1.mem)) ∧
    (s1.cutPoisoned = true →
      ∀ i : Nat, i < 32 → s1.mem (UInt64.ofNat 0x180 + UInt64.ofNat i) = 0)
  sim_ok {s1 s1' s2 req out} hRel hStep1 := by
    rcases hRel with ⟨hPolLen, hAuthLen, hMemPol, hMemAuth, hWin, hVCap, hAcc, hBurn,
      hRecip, hPTx, hBelt, hCutP, hShP, hSess, hShareEq, _⟩
    rcases hSess with ⟨hSTag, hSCom, hBAlp, hBKey, hQCfg⟩
    dsimp only [layer1CompiledElfMachine, layer2MirGuardedMachine, PartyMachine.ofOutcome] at hStep1 ⊢
    cases hQuar1 : (s1.cutPoisoned || s1.belt.poisoned || !s1.sharePresent)
    · have hCP0 : s1.cutPoisoned = false := by
        cases hc : s1.cutPoisoned <;> simp [hc] at hQuar1; rfl
      have hBP0 : s1.belt.poisoned = false := by
        cases hb : s1.belt.poisoned <;> simp [hCP0, hb] at hQuar1; rfl
      have hSP1 : s1.sharePresent = true := by
        cases hs : s1.sharePresent <;> simp [hCP0, hBP0, hs] at hQuar1; rfl
      have hSomeSh : s2.shareBytes = some (readShareMem32 s1.mem) := hShareEq hCP0 hBP0 hSP1
      have hQuar2 : (s2.cut.poisoned || s2.belt.poisoned || s2.shareBytes.isNone) = false := by
        rw [← hCutP, ← hBelt, hCP0, hBP0, hSomeSh]; rfl
      rw [hQuar1] at hStep1
      rw [hQuar2]
      simp only [Bool.false_eq_true, ↓reduceIte] at hStep1 ⊢
      have hElfPol :
          execElfCtEq32 s1.mem (UInt64.ofNat 0x100) req.tx.policyDigest =
            decide (req.tx.policyDigest = s2.policy.pinnedPolicyDigest) :=
        execElfCtEq32_spec hPolLen (by omega) hMemPol
      have hElfAuth :
          execElfCtEq32 s1.mem (UInt64.ofNat 0x140) req.tx.authorityDigest =
            decide (req.tx.authorityDigest = s2.policy.pinnedAuthorityDigest) :=
        execElfCtEq32_spec hAuthLen (by omega) hMemAuth
      rw [hElfPol, hElfAuth, hWin, hVCap, hAcc, hBurn, hRecip, hPTx, hBelt,
          hSTag, hSCom, hBAlp, hBKey, hQCfg] at hStep1
      have hBnePol :
          (!decide (req.tx.policyDigest = s2.policy.pinnedPolicyDigest)) =
            (req.tx.policyDigest != s2.policy.pinnedPolicyDigest) := by
        if hEq : req.tx.policyDigest = s2.policy.pinnedPolicyDigest then
          simp [hEq]
        else
          simp [hEq, bne, beq_false_of_ne hEq]
      have hBneAuth :
          (!decide (req.tx.authorityDigest = s2.policy.pinnedAuthorityDigest)) =
            (req.tx.authorityDigest != s2.policy.pinnedAuthorityDigest) := by
        if hEq : req.tx.authorityDigest = s2.policy.pinnedAuthorityDigest then
          simp [hEq]
        else
          simp [hEq, bne, beq_false_of_ne hEq]
      rw [hBnePol, hBneAuth] at hStep1
      unfold mirPolicyStep
      cases hW : (req.tx.windowId != s2.policy.windowId)
      · rw [hW] at hStep1; simp only [Bool.false_eq_true, ↓reduceIte] at hStep1 ⊢
        cases hP : (req.tx.policyDigest != s2.policy.pinnedPolicyDigest)
        · rw [hP] at hStep1; simp only [Bool.false_eq_true, ↓reduceIte] at hStep1 ⊢
          cases hA : (req.tx.authorityDigest != s2.policy.pinnedAuthorityDigest)
          · rw [hA] at hStep1; simp only [Bool.false_eq_true, ↓reduceIte] at hStep1 ⊢
            if hR : ¬ (req.tx.recipient ∈ s2.policy.allowedRecipients) then
              simp [hR] at hStep1
            else
              simp only [hR, ↓reduceIte] at hStep1 ⊢
              if hPT : ¬ (req.tx.amountUnits.toNat ≤ s2.policy.perTxCap.toNat) then
                simp [hPT] at hStep1
              else
                simp only [hPT, ↓reduceIte] at hStep1 ⊢
                if hVC : ¬ (req.tx.amountUnits.toNat ≤ (s2.policy.velocityWindowCap - s2.policy.accumulatedSpend).toNat) then
                  simp [hVC] at hStep1
                else
                  simp only [hVC, ↓reduceIte] at hStep1 ⊢
                  cases hN : u64MemBool req.tx.nonce s2.policy.burnedNonces
                  · rw [hN] at hStep1
                    simp only [Bool.false_eq_true, ↓reduceIte] at hStep1 ⊢
                    cases hQ : verifyFourLayerQuorumCert s2.quorumCertConfig q pkDigest
                        (encodeTransactionIntent req.tx.toTransactionIntent) req
                    · rw [hQ] at hStep1; simp at hStep1
                    · rw [hQ] at hStep1
                      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hStep1 ⊢
                      cases hE : (decide (pkDigest = s2.belt.enrolledPkDigest) && (req.reqEpoch == s2.belt.nextEpoch))
                      · rw [hE] at hStep1; simp at hStep1
                      · rw [hE] at hStep1
                        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hStep1 ⊢
                        cases hC : verifyPreCutTranscript s2.activeSessionTag s2.storedRound1Commits
                            s2.verifierBginAlpha s2.verifierBginKeyOffsets req.quorum
                            req.round1Openings req.round2Wires
                        · rw [hC] at hStep1; simp at hStep1
                        · rw [hC] at hStep1
                          rw [hSomeSh]
                          simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte,
                            Option.some.injEq, Prod.mk.injEq] at hStep1 ⊢
                          rcases hStep1 with ⟨rfl, rfl⟩
                          exact ⟨rfl, hPolLen, hAuthLen, hMemPol, hMemAuth, rfl, rfl, rfl, rfl,
                            rfl, rfl, rfl, hCP0, hSP1, ⟨rfl, rfl, rfl, rfl, rfl⟩,
                            fun _ _ _ => rfl,
                            fun hT => absurd hT (by rw [hCP0]; decide)⟩
                  · rw [hN] at hStep1; simp at hStep1
          · rw [hA] at hStep1; simp at hStep1
        · rw [hP] at hStep1; simp at hStep1
      · rw [hW] at hStep1; simp at hStep1
    · rw [hQuar1] at hStep1; simp at hStep1
  sim_err {s1 s2 req} hRel hNone1 := by
    have hRelSaved := hRel
    rcases hRel with ⟨hPolLen, hAuthLen, hMemPol, hMemAuth, hWin, hVCap, hAcc, hBurn,
      hRecip, hPTx, hBelt, hCutP, hShP, hSess, hShareEq, _⟩
    rcases hSess with ⟨hSTag, hSCom, hBAlp, hBKey, hQCfg⟩
    dsimp only [layer1CompiledElfMachine, layer2MirGuardedMachine, PartyMachine.ofOutcome] at hNone1 ⊢
    obtain ⟨hZeroMem, hPresBelow⟩ := execElfMemzeroShare32_spec s1.mem
    have hMemPolZero : ∀ i : Nat, i < 32 →
        execElfMemzeroShare32 s1.mem (UInt64.ofNat 0x100 + UInt64.ofNat i) =
          s2.policy.pinnedPolicyDigest.getD i 0 := by
      intro i hi
      have hLt : (UInt64.ofNat 0x100 + UInt64.ofNat i).toNat < 0x180 := by
        rw [addr_offset_toNat (base := 0x100) (i := i) (by omega)]; omega
      rw [hPresBelow _ hLt, hMemPol i hi]
    have hMemAuthZero : ∀ i : Nat, i < 32 →
        execElfMemzeroShare32 s1.mem (UInt64.ofNat 0x140 + UInt64.ofNat i) =
          s2.policy.pinnedAuthorityDigest.getD i 0 := by
      intro i hi
      have hLt : (UInt64.ofNat 0x140 + UInt64.ofNat i).toNat < 0x180 := by
        rw [addr_offset_toNat (base := 0x140) (i := i) (by omega)]; omega
      rw [hPresBelow _ hLt, hMemAuth i hi]
    have hQuarEq :
        (s2.cut.poisoned || s2.belt.poisoned || s2.shareBytes.isNone) =
          (s1.cutPoisoned || s1.belt.poisoned || !s1.sharePresent) := by
      have hNoneNotSome : s2.shareBytes.isNone = !s1.sharePresent := by
        rw [hShP]; cases s2.shareBytes <;> rfl
      rw [← hCutP, ← hBelt, hNoneNotSome]
    rw [hQuarEq]
    cases hQuar1 : (s1.cutPoisoned || s1.belt.poisoned || !s1.sharePresent)
    · have hCP0 : s1.cutPoisoned = false := by
        cases hc : s1.cutPoisoned <;> simp [hc] at hQuar1; rfl
      have hBP0 : s1.belt.poisoned = false := by
        cases hb : s1.belt.poisoned <;> simp [hCP0, hb] at hQuar1; rfl
      have hSP1 : s1.sharePresent = true := by
        cases hs : s1.sharePresent <;> simp [hCP0, hBP0, hs] at hQuar1; rfl
      rw [hQuar1] at hNone1
      simp only [Bool.false_eq_true, ↓reduceIte] at hNone1 ⊢
      have hElfPol :
          execElfCtEq32 s1.mem (UInt64.ofNat 0x100) req.tx.policyDigest =
            decide (req.tx.policyDigest = s2.policy.pinnedPolicyDigest) :=
        execElfCtEq32_spec hPolLen (by omega) hMemPol
      have hElfAuth :
          execElfCtEq32 s1.mem (UInt64.ofNat 0x140) req.tx.authorityDigest =
            decide (req.tx.authorityDigest = s2.policy.pinnedAuthorityDigest) :=
        execElfCtEq32_spec hAuthLen (by omega) hMemAuth
      have hBnePol :
          (!decide (req.tx.policyDigest = s2.policy.pinnedPolicyDigest)) =
            (req.tx.policyDigest != s2.policy.pinnedPolicyDigest) := by
        if hEq : req.tx.policyDigest = s2.policy.pinnedPolicyDigest then simp [hEq]
        else simp [hEq, bne, beq_false_of_ne hEq]
      have hBneAuth :
          (!decide (req.tx.authorityDigest = s2.policy.pinnedAuthorityDigest)) =
            (req.tx.authorityDigest != s2.policy.pinnedAuthorityDigest) := by
        if hEq : req.tx.authorityDigest = s2.policy.pinnedAuthorityDigest then simp [hEq]
        else simp [hEq, bne, beq_false_of_ne hEq]
      rw [hElfPol, hElfAuth, hBnePol, hBneAuth, hWin, hVCap, hAcc, hBurn, hRecip, hPTx, hBelt,
          hSTag, hSCom, hBAlp, hBKey, hQCfg] at hNone1 ⊢
      unfold mirPolicyStep
      cases hW : (req.tx.windowId != s2.policy.windowId)
      · rw [hW] at hNone1
        simp only [Bool.false_eq_true, ↓reduceIte] at hNone1 ⊢
        cases hP : (req.tx.policyDigest != s2.policy.pinnedPolicyDigest)
        · rw [hP] at hNone1
          simp only [Bool.false_eq_true, ↓reduceIte] at hNone1 ⊢
          cases hA : (req.tx.authorityDigest != s2.policy.pinnedAuthorityDigest)
          · rw [hA] at hNone1
            simp only [Bool.false_eq_true, ↓reduceIte] at hNone1 ⊢
            if hR : ¬ (req.tx.recipient ∈ s2.policy.allowedRecipients) then
              rw [ite_eq_left hR, ite_eq_left hR]; dsimp only; exact ⟨rfl, hRelSaved⟩
            else
              simp only [hR, ↓reduceIte] at hNone1 ⊢
              if hPT : ¬ (req.tx.amountUnits.toNat ≤ s2.policy.perTxCap.toNat) then
                rw [ite_eq_left hPT, ite_eq_left hPT]; dsimp only; exact ⟨rfl, hRelSaved⟩
              else
                simp only [hPT, ↓reduceIte] at hNone1 ⊢
                if hVC : ¬ (req.tx.amountUnits.toNat ≤ (s2.policy.velocityWindowCap - s2.policy.accumulatedSpend).toNat) then
                  rw [ite_eq_left hVC, ite_eq_left hVC]; dsimp only; exact ⟨rfl, hRelSaved⟩
                else
                  simp only [hVC, ↓reduceIte] at hNone1 ⊢
                  cases hN : u64MemBool req.tx.nonce s2.policy.burnedNonces
                  · rw [hN] at hNone1
                    simp only [Bool.false_eq_true, ↓reduceIte] at hNone1 ⊢
                    cases hQ : verifyFourLayerQuorumCert s2.quorumCertConfig q pkDigest
                        (encodeTransactionIntent req.tx.toTransactionIntent) req
                    · rw [ite_eq_left Bool.not_false, ite_eq_left Bool.not_false]
                      dsimp only; exact ⟨rfl, hRelSaved⟩
                    · rw [hQ] at hNone1
                      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hNone1 ⊢
                      cases hE : (decide (pkDigest = s2.belt.enrolledPkDigest) && (req.reqEpoch == s2.belt.nextEpoch))
                      · rw [ite_eq_left Bool.not_false, ite_eq_left Bool.not_false]
                        dsimp only; exact ⟨rfl, hRelSaved⟩
                      · rw [hE] at hNone1
                        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hNone1 ⊢
                        cases hC : verifyPreCutTranscript s2.activeSessionTag s2.storedRound1Commits
                            s2.verifierBginAlpha s2.verifierBginKeyOffsets req.quorum
                            req.round1Openings req.round2Wires
                        · rw [ite_eq_left Bool.not_false, ite_eq_left Bool.not_false]
                          dsimp only
                          exact ⟨rfl, hPolLen, hAuthLen, hMemPolZero, hMemAuthZero, rfl, rfl,
                            rfl, rfl, rfl, rfl, rfl,
                            rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩,
                            fun hF => absurd hF (by decide), fun _ => hZeroMem⟩
                        · have hSomeSh : s2.shareBytes = some (readShareMem32 s1.mem) := hShareEq hCP0 hBP0 hSP1
                          rw [hC] at hNone1
                          simp at hNone1
                  · rw [ite_eq_left (rfl : true = true), ite_eq_left (rfl : true = true)]
                    dsimp only; exact ⟨rfl, hRelSaved⟩
          · rw [ite_eq_left (rfl : true = true), ite_eq_left (rfl : true = true)]
            dsimp only; exact ⟨rfl, hRelSaved⟩
        · rw [ite_eq_left (rfl : true = true), ite_eq_left (rfl : true = true)]
          dsimp only; exact ⟨rfl, hRelSaved⟩
      · rw [ite_eq_left (rfl : true = true), ite_eq_left (rfl : true = true)]
        dsimp only; exact ⟨rfl, hRelSaved⟩
    · rw [ite_eq_left (rfl : true = true), ite_eq_left (rfl : true = true)]
      dsimp only
      exact ⟨rfl, hPolLen, hAuthLen, hMemPolZero, hMemAuthZero, hWin, hVCap,
        hAcc, hBurn, hRecip, hPTx, congrArg (fun b => { b with poisoned := true }) hBelt,
        rfl, rfl, ⟨hSTag, hSCom, hBAlp, hBKey, hQCfg⟩,
        fun hF => absurd hF (by decide), fun _ => hZeroMem⟩

private theorem sim12_zeroIfPoisoned {n : Nat} {q : Nat} {pkDigest : List UInt8}
    {signFromShare : List UInt8 → List UInt8 → ByteArray}
    {s1 : Layer1ElfState} {s2 : Layer2MirState}
    (hRel : (sim_layer1_to_layer2 (n := n) q pkDigest signFromShare).Rel s1 s2) :
    s1.cutPoisoned = true →
      ∀ i : Nat, i < 32 → s1.mem (UInt64.ofNat 0x180 + UInt64.ofNat i) = 0 := by
  rcases hRel with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hZero⟩
  exact hZero

private theorem quorumGate23_eq {PK : Type} {n q f : Nat}
    (corrupt : List (Fin n)) (pkDigestOf : PK → List UInt8) (pk : PK)
    (cfg : QuorumCertConfig) (msgBytes : List UInt8) (req : FourLayerReq n)
    (tsig : IdealTsigState PK (List UInt8))
    (hPk : tsig.pk = pk) (hNP : tsig.numParties = n) (hTh : tsig.threshold = q)
    (hCorr1 : tsig.corruptParties = corrupt.map Fin.val)
    (hCorr2 : tsig.identifiedCheaters = [])
    (hBound : n + f < 2 * q) (hQPos : 0 < q) (hQLeN : q ≤ n)
    (hCorruptNd : corrupt.Nodup) (hCorruptLe : corrupt.length ≤ f) :
    (verifyFourLayerQuorumCert cfg tsig.threshold (pkDigestOf tsig.pk) msgBytes req &&
      validThresholdApproval tsig
        ((req.quorum.filter (fun p => !finMemBool p corrupt)).map Fin.val)) =
    verifyFourLayerQuorumCert cfg q (pkDigestOf pk) msgBytes req := by
  rw [hPk, hTh]
  cases hV : verifyFourLayerQuorumCert cfg q (pkDigestOf pk) msgBytes req
  · simp
  · simp only [Bool.true_and]
    obtain ⟨hNd, hLen⟩ := verifyFourLayerQuorumCert_implies_nodup_and_len hV
    exact (mirBeltLatch_quorum_discharges_idealTsig_approval
      corrupt req.quorum tsig hNP hTh hQPos hQLeN hCorr1 hCorr2
      hCorruptNd hCorruptLe hBound hNd hLen).1

/-- **Link 2 (`sim_layer2_to_layer3`)**:
    `ForwardSim` from fixed-width `layer2MirGuardedMachine` (`UInt64` policy + `2 * q > n + f`
    `MirBeltLatchState` + sticky `MirRssCutSession`) to `layer3InteractiveProtocolMachine`. -/
def sim_layer2_to_layer3 {PK : Type} {n q f : Nat}
    (corrupt : List (Fin n)) (pkDigestOf : PK → List UInt8)
    (pk : PK)
    (dealtShares : Nat → Option (List UInt8))
    (custodianShare : List UInt8)
    (signFromShare : List UInt8 → List UInt8 → ByteArray)
    (assembleThresholdSig : (Nat → Option (List UInt8)) → List UInt8 → ByteArray)
    (_hBound : n + f < 2 * q)
    (_hQPos : 0 < q) (_hQLeN : q ≤ n)
    (_hCorruptNd : corrupt.Nodup) (_hCorruptLe : corrupt.length ≤ f)
    (_hSigMatch : ∀ msg : List UInt8, assembleThresholdSig dealtShares msg = signFromShare custodianShare msg) :
    ForwardSim
      (layer2MirGuardedMachine q (pkDigestOf pk) signFromShare)
      (layer3InteractiveProtocolMachine corrupt pkDigestOf assembleThresholdSig) where
  Rel s2 s3 :=
    s2.policy.accumulatedSpend.toNat ≤ s2.policy.velocityWindowCap.toNat ∧
    s2.policy.toStatefulPolicyGuard = s3.policy ∧
    s3.cluster.tsig.pk = pk ∧
    s3.cluster.tsig.numParties = n ∧
    s3.cluster.tsig.threshold = q ∧
    (s3.cluster.tsig.corruptParties = corrupt.map Fin.val ∧
      s3.cluster.tsig.identifiedCheaters = []) ∧
    s2.belt.enrolledPkDigest = s3.cluster.honestWal.enrolledPkDigest ∧
    s2.belt.nextEpoch = s3.cluster.honestWal.nextEpoch ∧
    s2.belt.latchedRecord = s3.cluster.honestWal.latchedRecord ∧
    s2.belt.poisoned = s3.cluster.honestWal.poisoned ∧
    s2.cut.poisoned = s3.cluster.honestWal.poisoned ∧
    Layer23SessionEq s2 s3 ∧
    (s3.cluster.honestWal.poisoned = false →
      s2.shareBytes = some custodianShare ∧ s3.cluster.honestShares = dealtShares)
  sim_ok {s2 s2' s3 req out} hRel hStep2 := by
    rcases hRel with ⟨hInvPol, hPolEq, hPk, hNP, hTh, hCorr, hWalPk, hWalEp, hWalLat,
      hBeltP, hCutP, hSess, hIntact⟩
    rcases hSess with ⟨hSTag, hSCom, hBAlp, hBKey, hQCfg⟩
    dsimp only [layer2MirGuardedMachine, layer3InteractiveProtocolMachine,
      PartyMachine.ofOutcome] at hStep2 ⊢
    cases hP3 : s3.cluster.honestWal.poisoned
    · obtain ⟨hSomeSh, hDealt⟩ := hIntact hP3
      have hQuar2 : (s2.cut.poisoned || s2.belt.poisoned || s2.shareBytes.isNone) = false := by
        rw [hCutP, hBeltP, hP3, hSomeSh]; rfl
      rw [hQuar2] at hStep2
      simp only [Bool.false_eq_true, ↓reduceIte] at hStep2 ⊢
      have hPolStep := mirPolicyGuard_lockstepSim.step_eq req.tx hInvPol
      dsimp only [mirPolicyGuard_lockstepSim, mirPolicyGuardMachine, specPolicyGuardMachine,
        PartyMachine.ofOption, PartyMachine.ofOutcome] at hPolStep
      cases hMirPol : mirPolicyStep s2.policy req.tx with
      | none => rw [hMirPol] at hStep2; cases hStep2
      | some polEnv =>
        rcases polEnv with ⟨pol2', env⟩
        rw [hMirPol] at hPolStep hStep2
        rcases hPolStep with ⟨hInvPol', hSpecPolOk⟩
        rw [hPolEq] at hSpecPolOk
        cases hPol3 : policyGuardStep s3.policy req.tx.toTransactionIntent with
        | rejected _ _ => rw [hPol3] at hSpecPolOk; cases hSpecPolOk
        | accepted pol3' env3 =>
          rw [hPol3] at hSpecPolOk
          dsimp only [CustodyStepOutcome.toStepOutcome] at hSpecPolOk
          injection hSpecPolOk with hPairPol
          rcases Prod.mk.inj hPairPol with ⟨hPolEq', hEnv⟩
          subst env3
          dsimp only at hStep2 ⊢
          rw [← hQCfg, quorumGate23_eq corrupt pkDigestOf pk s2.quorumCertConfig env.canonicalBytes
            req s3.cluster.tsig hPk hNP hTh hCorr.1 hCorr.2 _hBound _hQPos _hQLeN _hCorruptNd _hCorruptLe]
          cases hQ2 : verifyFourLayerQuorumCert s2.quorumCertConfig q (pkDigestOf pk) env.canonicalBytes req
          · rw [hQ2] at hStep2; simp at hStep2
          · rw [hQ2] at hStep2
            simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hStep2 ⊢
            rw [hPk, ← hWalPk, ← hWalEp, ← hSTag, ← hSCom, ← hBAlp, ← hBKey]
            cases hE : (decide (pkDigestOf pk = s2.belt.enrolledPkDigest) && (req.reqEpoch == s2.belt.nextEpoch))
            · rw [hE] at hStep2; simp at hStep2
            · rw [hE] at hStep2
              simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hStep2 ⊢
              cases hC : verifyPreCutTranscript s2.activeSessionTag s2.storedRound1Commits
                  s2.verifierBginAlpha s2.verifierBginKeyOffsets req.quorum
                  req.round1Openings req.round2Wires
              · rw [hC] at hStep2; simp at hStep2
              · rw [hC, hSomeSh] at hStep2
                simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte,
                  Option.some.injEq, Prod.mk.injEq] at hStep2
                rcases hStep2 with ⟨rfl, rfl⟩
                rw [ite_eq_right (by decide : ¬ ((!true) = true))]
                dsimp only
                rw [hDealt, _hSigMatch]
                exact ⟨rfl, hInvPol', hPolEq'.symm, rfl, hNP, hTh, hCorr, rfl, rfl, rfl,
                  hBeltP.trans hP3, rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ => ⟨rfl, rfl⟩⟩
    · have hQuar2 : (s2.cut.poisoned || s2.belt.poisoned || s2.shareBytes.isNone) = true := by
        rw [hCutP, hP3]; rfl
      rw [hQuar2] at hStep2
      simp at hStep2
  sim_err {s2 s3 req} hRel hNone2 := by
    have hRelSaved := hRel
    rcases hRel with ⟨hInvPol, hPolEq, hPk, hNP, hTh, hCorr, hWalPk, hWalEp, hWalLat,
      hBeltP, hCutP, hSess, hIntact⟩
    rcases hSess with ⟨hSTag, hSCom, hBAlp, hBKey, hQCfg⟩
    dsimp only [layer2MirGuardedMachine, layer3InteractiveProtocolMachine,
      PartyMachine.ofOutcome] at hNone2 ⊢
    cases hP3 : s3.cluster.honestWal.poisoned
    · obtain ⟨hSomeSh, _⟩ := hIntact hP3
      have hQuar2 : (s2.cut.poisoned || s2.belt.poisoned || s2.shareBytes.isNone) = false := by
        rw [hCutP, hBeltP, hP3, hSomeSh]; rfl
      rw [hQuar2] at hNone2 ⊢
      simp only [Bool.false_eq_true, ↓reduceIte] at hNone2 ⊢
      have hPolStep := mirPolicyGuard_lockstepSim.step_eq req.tx hInvPol
      dsimp only [mirPolicyGuard_lockstepSim, mirPolicyGuardMachine, specPolicyGuardMachine,
        PartyMachine.ofOption, PartyMachine.ofOutcome] at hPolStep
      cases hMirPol : mirPolicyStep s2.policy req.tx with
      | none =>
        rw [hMirPol] at hPolStep
        rcases hPolStep with ⟨_, hPolNone, _⟩
        rw [hPolEq] at hPolNone
        cases hPol3 : policyGuardStep s3.policy req.tx.toTransactionIntent with
        | accepted _ _ => rw [hPol3] at hPolNone; cases hPolNone
        | rejected _ _ => dsimp only; exact ⟨rfl, hRelSaved⟩
      | some polEnv =>
        rcases polEnv with ⟨pol2', env⟩
        rw [hMirPol] at hPolStep hNone2
        rcases hPolStep with ⟨_, hSpecPolOk⟩
        rw [hPolEq] at hSpecPolOk
        cases hPol3 : policyGuardStep s3.policy req.tx.toTransactionIntent with
        | rejected _ _ => rw [hPol3] at hSpecPolOk; cases hSpecPolOk
        | accepted pol3' env3 =>
          rw [hPol3] at hSpecPolOk
          dsimp only [CustodyStepOutcome.toStepOutcome] at hSpecPolOk
          injection hSpecPolOk with hPairPol
          rcases Prod.mk.inj hPairPol with ⟨_, hEnv⟩
          subst env3
          dsimp only at hNone2 ⊢
          rw [← hQCfg, quorumGate23_eq corrupt pkDigestOf pk s2.quorumCertConfig env.canonicalBytes
            req s3.cluster.tsig hPk hNP hTh hCorr.1 hCorr.2 _hBound _hQPos _hQLeN _hCorruptNd _hCorruptLe]
          cases hQ2 : verifyFourLayerQuorumCert s2.quorumCertConfig q (pkDigestOf pk) env.canonicalBytes req
          · rw [ite_eq_left Bool.not_false, ite_eq_left Bool.not_false]
            dsimp only; exact ⟨rfl, hRelSaved⟩
          · rw [hQ2] at hNone2
            simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hNone2 ⊢
            rw [hPk, ← hWalPk, ← hWalEp, ← hSTag, ← hSCom, ← hBAlp, ← hBKey]
            cases hE : (decide (pkDigestOf pk = s2.belt.enrolledPkDigest) && (req.reqEpoch == s2.belt.nextEpoch))
            · rw [ite_eq_left Bool.not_false, ite_eq_left Bool.not_false]
              dsimp only; exact ⟨rfl, hRelSaved⟩
            · rw [hE] at hNone2
              simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hNone2 ⊢
              cases hC : verifyPreCutTranscript s2.activeSessionTag s2.storedRound1Commits
                  s2.verifierBginAlpha s2.verifierBginKeyOffsets req.quorum
                  req.round1Openings req.round2Wires
              · rw [ite_eq_left Bool.not_false, ite_eq_left Bool.not_false]
                dsimp only [poisonRealCluster, walQuarantine]
                exact ⟨rfl, hInvPol, hPolEq, hPk, hNP, hTh, hCorr, hWalPk, hWalEp, hWalLat,
                  rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩, fun hF => absurd hF (by decide)⟩
              · rw [hC, hSomeSh] at hNone2
                simp at hNone2
    · have hQuar2 : (s2.cut.poisoned || s2.belt.poisoned || s2.shareBytes.isNone) = true := by
        rw [hCutP, hP3]; rfl
      rw [hQuar2]
      rw [ite_eq_left (rfl : true = true), ite_eq_left (rfl : true = true)]
      dsimp only [poisonRealCluster, walQuarantine]
      exact ⟨rfl, hInvPol, hPolEq, hPk, hNP, hTh, hCorr, hWalPk, hWalEp, hWalLat,
        rfl, rfl, ⟨hSTag, hSCom, hBAlp, hBKey, hQCfg⟩, fun hF => absurd hF (by decide)⟩

/-- **Link 3 (`sim_layer3_to_layer4`)**:
    Conditional `ForwardSim` from `layer3InteractiveProtocolMachine` (with secret shares) to
    share-free `layer4IdealTsigMachine` parameterized by the threshold reconstruction equation
    `_hOracleEq`. -/
def sim_layer3_to_layer4 {PK : Type} {n : Nat}
    (corrupt : List (Fin n)) (pkDigestOf : PK → List UInt8)
    (dealtShares : Nat → Option (List UInt8))
    (assembleThresholdSig : (Nat → Option (List UInt8)) → List UInt8 → ByteArray)
    (idealSignOracle : List UInt8 → ByteArray)
    (_hOracleEq : ∀ msg : List UInt8, assembleThresholdSig dealtShares msg = idealSignOracle msg) :
    ForwardSim
      (layer3InteractiveProtocolMachine corrupt pkDigestOf assembleThresholdSig)
      (layer4IdealTsigMachine corrupt pkDigestOf idealSignOracle) where
  Rel s3 s4 :=
    s3.policy = s4.policy ∧
    s3.cluster.tsig = s4.ideal.tsig ∧
    s3.cluster.honestWal = s4.ideal.honestWal ∧
    s3.cluster.maskSessionCursor = s4.ideal.maskSessionCursor ∧
    Layer34SessionEq s3 s4 ∧
    (s3.cluster.honestWal.poisoned = false → s3.cluster.honestShares = dealtShares)
  sim_ok {s3 s3' s4 req out} hRel hStep3 := by
    rcases s3 with ⟨pol, ⟨tsig, ⟨wPk, wEp, wLat, wPois⟩, cur, shares3⟩, aTag, sCom, vAlp, vKey, qCfg⟩
    rcases s4 with ⟨pol4, ⟨tsig4, wal4, cur4⟩, aTag4, sCom4, vAlp4, vKey4, qCfg4⟩
    dsimp only [Layer34SessionEq] at hRel
    rcases hRel with ⟨rfl, rfl, rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩, hSh⟩
    dsimp only [layer3InteractiveProtocolMachine, layer4IdealTsigMachine,
      PartyMachine.ofOutcome] at hStep3 ⊢
    cases wPois
    · have hDealt : shares3 = dealtShares := hSh rfl
      simp only [Bool.false_eq_true, ↓reduceIte] at hStep3 ⊢
      cases hPG : policyGuardStep pol req.tx.toTransactionIntent with
      | rejected _ _ => rw [hPG] at hStep3; simp at hStep3
      | accepted pol' env =>
        rw [hPG] at hStep3
        dsimp only at hStep3 ⊢
        cases hQ : (verifyFourLayerQuorumCert qCfg tsig.threshold (pkDigestOf tsig.pk) env.canonicalBytes req &&
            validThresholdApproval tsig
              ((req.quorum.filter (fun p => !finMemBool p corrupt)).map Fin.val))
        · rw [hQ] at hStep3; simp at hStep3
        · rw [hQ] at hStep3
          simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hStep3 ⊢
          cases hE : (decide (pkDigestOf tsig.pk = wPk) && (req.reqEpoch == wEp))
          · rw [hE] at hStep3; simp at hStep3
          · rw [hE] at hStep3
            simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hStep3 ⊢
            cases hC : verifyPreCutTranscript aTag sCom vAlp vKey req.quorum
                req.round1Openings req.round2Wires
            · rw [hC] at hStep3; simp at hStep3
            · rw [hC] at hStep3
              simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte,
                Option.some.injEq, Prod.mk.injEq] at hStep3
              rcases hStep3 with ⟨rfl, rfl⟩
              rw [ite_eq_right (by decide : ¬ ((!true) = true))]
              dsimp only
              rw [hDealt, _hOracleEq]
              exact ⟨rfl, rfl, rfl, rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ => rfl⟩
    · simp at hStep3
  sim_err {s3 s4 req} hRel hNone3 := by
    rcases s3 with ⟨pol, ⟨tsig, ⟨wPk, wEp, wLat, wPois⟩, cur, shares3⟩, aTag, sCom, vAlp, vKey, qCfg⟩
    rcases s4 with ⟨pol4, ⟨tsig4, wal4, cur4⟩, aTag4, sCom4, vAlp4, vKey4, qCfg4⟩
    dsimp only [Layer34SessionEq] at hRel
    rcases hRel with ⟨rfl, rfl, rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩, hSh⟩
    dsimp only [layer3InteractiveProtocolMachine, layer4IdealTsigMachine,
      PartyMachine.ofOutcome] at hNone3 ⊢
    cases wPois
    · have hDealt : shares3 = dealtShares := hSh rfl
      simp only [Bool.false_eq_true, ↓reduceIte] at hNone3 ⊢
      cases hPG : policyGuardStep pol req.tx.toTransactionIntent with
      | rejected _ _ => exact ⟨rfl, rfl, rfl, rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ => hDealt⟩
      | accepted pol' env =>
        rw [hPG] at hNone3
        dsimp only at hNone3 ⊢
        cases hQ : (verifyFourLayerQuorumCert qCfg tsig.threshold (pkDigestOf tsig.pk) env.canonicalBytes req &&
            validThresholdApproval tsig
              ((req.quorum.filter (fun p => !finMemBool p corrupt)).map Fin.val))
        · rw [ite_eq_left Bool.not_false, ite_eq_left Bool.not_false]
          dsimp only
          exact ⟨rfl, rfl, rfl, rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ => hDealt⟩
        · rw [hQ] at hNone3
          simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hNone3 ⊢
          cases hE : (decide (pkDigestOf tsig.pk = wPk) && (req.reqEpoch == wEp))
          · rw [ite_eq_left Bool.not_false, ite_eq_left Bool.not_false]
            dsimp only
            exact ⟨rfl, rfl, rfl, rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ => hDealt⟩
          · rw [hE] at hNone3
            simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hNone3 ⊢
            cases hC : verifyPreCutTranscript aTag sCom vAlp vKey req.quorum
                req.round1Openings req.round2Wires
            · rw [ite_eq_left Bool.not_false, ite_eq_left Bool.not_false]
              dsimp only [poisonRealCluster, poisonIdealCluster, walQuarantine]
              exact ⟨rfl, rfl, rfl, rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩,
                fun hF => absurd hF (by decide)⟩
            · rw [hC] at hNone3; simp at hNone3
    · rw [ite_eq_left (rfl : true = true), ite_eq_left (rfl : true = true)]
      dsimp only [poisonRealCluster, poisonIdealCluster, walQuarantine]
      exact ⟨rfl, rfl, rfl, rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩,
        fun hF => absurd hF (by decide)⟩

/-- **Conditional 4-Layer Control-Flow & Authorization Refinement (`isa_to_mir_to_protocol_to_ideal_sim`)**:
    Composes `ForwardSim.trans` across:
    `(1) Compiled ELF ISA Slice` $\to$ `(2) Fixed-Width Guard Model` $\to$
    `(3) Centralized Threshold Transition Model` $\to$ `(4) Share-Free Target Authorization Model`.
    Explicitly parameterized by the threshold reconstruction contracts `hSigMatch` and `hOracleEq`
    (which are discharged algebraically via multi-share Lagrange interpolation in
    `inhabited_four_layer_chain`, while cryptographic UC simulation lives in
    `InteractiveUcEngine.lean`). -/
@[expose]
def isa_to_mir_to_protocol_to_ideal_sim {PK : Type} {n q f : Nat}
    (corrupt : List (Fin n)) (pkDigestOf : PK → List UInt8)
    (pk : PK)
    (dealtShares : Nat → Option (List UInt8))
    (custodianShare : List UInt8)
    (signFromShare : List UInt8 → List UInt8 → ByteArray)
    (assembleThresholdSig : (Nat → Option (List UInt8)) → List UInt8 → ByteArray)
    (idealSignOracle : List UInt8 → ByteArray)
    (hBound : n + f < 2 * q)
    (hQPos : 0 < q) (hQLeN : q ≤ n)
    (hCorruptNd : corrupt.Nodup) (hCorruptLe : corrupt.length ≤ f)
    (hSigMatch : ∀ msg : List UInt8, assembleThresholdSig dealtShares msg = signFromShare custodianShare msg)
    (hOracleEq : ∀ msg : List UInt8, assembleThresholdSig dealtShares msg = idealSignOracle msg) :
    ForwardSim
      (layer1CompiledElfMachine (n := n) q (pkDigestOf pk) (fun m msg => signFromShare (readShareMem32 m) msg))
      (layer4IdealTsigMachine corrupt pkDigestOf idealSignOracle) :=
  (sim_layer1_to_layer2 (n := n) q (pkDigestOf pk) signFromShare).trans
    ((sim_layer2_to_layer3 corrupt pkDigestOf pk dealtShares custodianShare
        signFromShare assembleThresholdSig hBound hQPos hQLeN hCorruptNd hCorruptLe hSigMatch).trans
      (sim_layer3_to_layer4 corrupt pkDigestOf dealtShares assembleThresholdSig idealSignOracle hOracleEq))

/-- Policy/epoch/quorum safety only: this predicate does not assert transcript MAC validity
    or signature authenticity. The Round-2 model reuses fixed keys across sessions.
    Multi-turn 4-layer transcript predicate:
    1. Cumulative approved `amount_units` stays within `velocityWindowCap` (never fooled by `callerEchoedSpent`),
    2. Approved intent nonces are strictly `Nodup`,
    3. Approved signing epochs are strictly increasing (`Pairwise (· < ·)`),
    4. Every approved request includes at least one honest validator `p ∈ req.quorum` with `p ∉ corrupt`. -/
def FourLayerTraceSafe {n : Nat} (velocityWindowCap : Nat) (corrupt : List (Fin n))
    (trace : List (FourLayerReq n × FourLayerOut)) : Prop :=
  let approvedAmts := trace.map (fun p => p.2.envelope.intent.amount_units)
  let approvedNonces := trace.map (fun p => p.2.envelope.intent.nonce)
  let approvedEpochs := trace.map (fun p => p.2.committedEpoch)
  approvedAmts.foldr (· + ·) 0 ≤ velocityWindowCap ∧
  approvedNonces.Nodup ∧
  approvedEpochs.Pairwise (· < ·) ∧
  (∀ p ∈ trace, ∃ h ∈ p.1.quorum, h ∉ corrupt)

private theorem layer4_validTrace_safe {PK : Type} {n : Nat}
    (corrupt : List (Fin n)) (pkDigestOf : PK → List UInt8)
    (idealSignOracle : List UInt8 → ByteArray)
    {s₀ sFinal : Layer4IdealState PK} {trace : List (FourLayerReq n × FourLayerOut)}
    (hCap : s₀.policy.accumulated_spend ≤ s₀.policy.velocity_window_cap)
    (hCorrEq : s₀.ideal.tsig.corruptParties = corrupt.map Fin.val)
    (hDishonest : s₀.ideal.tsig.corruptParties.length + 1 ≤ s₀.ideal.tsig.threshold)
    (hTr : (layer4IdealTsigMachine corrupt pkDigestOf idealSignOracle).ValidTrace s₀ trace sFinal) :
    ValidCustodyTrace policyGuardStep s₀.policy
      (trace.map (fun p => (p.1.tx.toTransactionIntent, some p.2.envelope))) sFinal.policy ∧
    s₀.ideal.honestWal.nextEpoch ≤ sFinal.ideal.honestWal.nextEpoch ∧
    (∀ p ∈ trace, s₀.ideal.honestWal.nextEpoch ≤ p.2.committedEpoch) ∧
    (trace.map (fun p => p.2.committedEpoch)).Pairwise (· < ·) ∧
    (∀ p ∈ trace, ∃ h ∈ p.1.quorum, h ∉ corrupt) := by
  revert hCap hCorrEq hDishonest
  induction hTr with
  | nil s₀ =>
    intro _ _ _
    refine ⟨.nil s₀.policy, Nat.le_refl _, ?_, List.Pairwise.nil, ?_⟩
    · intro _ hm; cases hm
    · intro _ hm; cases hm
  | @accept s₀ s₁ sFinal req out rest hStep _ ih =>
    intro hCap hCorrEq hDishonest
    dsimp only [layer4IdealTsigMachine, PartyMachine.ofOutcome] at hStep
    cases hP : s₀.ideal.honestWal.poisoned
    · rw [hP] at hStep
      simp only [Bool.false_eq_true, ↓reduceIte] at hStep
      cases hPG : policyGuardStep s₀.policy req.tx.toTransactionIntent with
      | rejected _ _ => rw [hPG] at hStep; cases hStep
      | accepted pol₁ env =>
        rw [hPG] at hStep
        dsimp only at hStep
        let honApp := (req.quorum.filter (fun p => !finMemBool p corrupt)).map Fin.val
        cases hQ : (verifyFourLayerQuorumCert s₀.quorumCertConfig s₀.ideal.tsig.threshold
            (pkDigestOf s₀.ideal.tsig.pk) env.canonicalBytes req &&
            validThresholdApproval s₀.ideal.tsig honApp)
        · rw [hQ] at hStep; simp at hStep
        · rw [hQ] at hStep
          simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hStep
          cases hE : (decide (pkDigestOf s₀.ideal.tsig.pk = s₀.ideal.honestWal.enrolledPkDigest) &&
              (req.reqEpoch == s₀.ideal.honestWal.nextEpoch))
          · rw [hE] at hStep; simp at hStep
          · rw [hE] at hStep
            simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hStep
            cases hC : verifyPreCutTranscript s₀.activeSessionTag s₀.storedRound1Commits
                s₀.verifierBginAlpha s₀.verifierBginKeyOffsets req.quorum
                req.round1Openings req.round2Wires
            · rw [hC] at hStep; simp at hStep
            · rw [hC] at hStep
              simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte,
                Option.some.injEq, Prod.mk.injEq] at hStep
              rcases hStep with ⟨rfl, rfl⟩
              have hEpEq : req.reqEpoch = s₀.ideal.honestWal.nextEpoch :=
                Nat.eq_of_beq_eq_true (Bool.and_eq_true_iff.mp hE).2
              have hCapEq : pol₁.velocity_window_cap = s₀.policy.velocity_window_cap := by
                unfold policyGuardStep at hPG
                if c1 : (req.tx.toTransactionIntent.window_id != s₀.policy.window_id) = true then simp [c1] at hPG
                else if c2 : (req.tx.toTransactionIntent.policy_digest != s₀.policy.pinned_policy_digest) = true then simp [c1, c2] at hPG
                else if c3 : (req.tx.toTransactionIntent.authority_digest != s₀.policy.pinned_authority_digest) = true then simp [c1, c2, c3] at hPG
                else if c4 : ¬ (req.tx.toTransactionIntent.recipient ∈ s₀.policy.allowed_recipients) then simp [c1, c2, c3, c4] at hPG
                else if c5 : ¬ (req.tx.toTransactionIntent.amount_units ≤ s₀.policy.per_tx_cap) then simp [c1, c2, c3, c4, c5] at hPG
                else if c6 : ¬ (s₀.policy.accumulated_spend + req.tx.toTransactionIntent.amount_units ≤ s₀.policy.velocity_window_cap) then simp [c1, c2, c3, c4, c5, c6] at hPG
                else if c7 : req.tx.toTransactionIntent.nonce ∈ s₀.policy.burned_intent_nonces then simp [c1, c2, c3, c4, c5, c6, c7] at hPG
                else
                  simp only [c1, c2, c3, c4, c5, c6, c7, Bool.false_eq_true, ↓reduceIte,
                    CustodyStepOutcome.accepted.injEq] at hPG
                  rcases hPG with ⟨rfl, _⟩; rfl
              have hPolCap₁ : pol₁.accumulated_spend ≤ pol₁.velocity_window_cap := by
                rw [hCapEq]
                exact (policy_multiturn_velocity_and_intent_binding hCap
                  (.consAccepted hPG (.nil pol₁))).2.1
              obtain ⟨hCustRest, hMonoRest, hGeRest, hPairRest, hHonRest⟩ :=
                ih hPolCap₁ hCorrEq hDishonest
              have hMonoStep : req.reqEpoch + 1 ≤ sFinal.ideal.honestWal.nextEpoch := hMonoRest
              have hValApp : validThresholdApproval s₀.ideal.tsig honApp = true :=
                (Bool.and_eq_true_iff.mp hQ).2
              obtain ⟨hVal, hhMem, _, hhNotC⟩ :=
                thresholdApproval_requires_honest_party s₀.ideal.tsig honApp hDishonest hValApp
              rcases List.mem_map.mp hhMem with ⟨pFin, hpFilt, hpValEq⟩
              have hpInQ : pFin ∈ req.quorum := mem_of_mem_filter_local hpFilt
              have hpNotCorrupt : pFin ∉ corrupt := by
                intro hc
                apply hhNotC
                rw [hCorrEq, ← hpValEq]
                exact List.mem_map_of_mem hc
              refine ⟨.consAccepted hPG hCustRest, by omega, ?_, ?_, ?_⟩
              · intro p hp
                rcases List.mem_cons.mp hp with rfl | hTail
                · exact Nat.le_of_eq hEpEq.symm
                · have h1 : req.reqEpoch + 1 ≤ p.2.committedEpoch := hGeRest p hTail
                  omega
              · simp only [List.map_cons, List.pairwise_cons]
                refine ⟨?_, hPairRest⟩
                intro ep₂ hep₂
                rcases List.mem_map.mp hep₂ with ⟨p₂, hp₂Mem, rfl⟩
                have h1 : req.reqEpoch + 1 ≤ p₂.2.committedEpoch := hGeRest p₂ hp₂Mem
                change req.reqEpoch < p₂.2.committedEpoch
                omega
              · intro p hp
                rcases List.mem_cons.mp hp with rfl | hTail
                · exact ⟨pFin, hpInQ, hpNotCorrupt⟩
                · exact hHonRest p hTail
    · rw [hP] at hStep; simp at hStep
  | @reject s₀ sFinal req rest hNone _ ih =>
    intro hCap hCorrEq hDishonest
    let sErr := (layer4IdealTsigMachine corrupt pkDigestOf idealSignOracle).errStep s₀ req
    have hPres :
        sErr.policy = s₀.policy ∧
        sErr.ideal.tsig = s₀.ideal.tsig ∧
        sErr.ideal.honestWal.nextEpoch = s₀.ideal.honestWal.nextEpoch := by
      dsimp only [sErr, layer4IdealTsigMachine, PartyMachine.ofOutcome] at hNone ⊢
      cases hP : s₀.ideal.honestWal.poisoned
      · rw [hP] at hNone
        simp only [Bool.false_eq_true, ↓reduceIte] at hNone ⊢
        cases hPG : policyGuardStep s₀.policy req.tx.toTransactionIntent with
        | rejected _ _ => exact ⟨rfl, rfl, rfl⟩
        | accepted pol' env =>
          rw [hPG] at hNone
          dsimp only at hNone ⊢
          let honApp := (req.quorum.filter (fun p => !finMemBool p corrupt)).map Fin.val
          cases hQ : (verifyFourLayerQuorumCert s₀.quorumCertConfig s₀.ideal.tsig.threshold
              (pkDigestOf s₀.ideal.tsig.pk) env.canonicalBytes req &&
              validThresholdApproval s₀.ideal.tsig honApp)
          · rw [ite_eq_left Bool.not_false]
            dsimp only
            exact ⟨rfl, rfl, rfl⟩
          · rw [hQ] at hNone
            simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hNone ⊢
            cases hE : (decide (pkDigestOf s₀.ideal.tsig.pk = s₀.ideal.honestWal.enrolledPkDigest) &&
                (req.reqEpoch == s₀.ideal.honestWal.nextEpoch))
            · rw [ite_eq_left Bool.not_false]
              dsimp only
              exact ⟨rfl, rfl, rfl⟩
            · rw [hE] at hNone
              simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hNone ⊢
              cases hC : verifyPreCutTranscript s₀.activeSessionTag s₀.storedRound1Commits
                  s₀.verifierBginAlpha s₀.verifierBginKeyOffsets req.quorum
                  req.round1Openings req.round2Wires
              · rw [ite_eq_left Bool.not_false]
                dsimp only [poisonIdealCluster, walQuarantine]
                exact ⟨rfl, rfl, rfl⟩
              · rw [hC] at hNone; simp at hNone
      · rw [ite_eq_left (rfl : true = true)]
        dsimp only [poisonIdealCluster, walQuarantine]
        exact ⟨rfl, rfl, rfl⟩
    have hCapErr : sErr.policy.accumulated_spend ≤ sErr.policy.velocity_window_cap := by
      rw [hPres.1]; exact hCap
    have hCorrErr : sErr.ideal.tsig.corruptParties = corrupt.map Fin.val := by
      rw [hPres.2.1]; exact hCorrEq
    have hDishErr : sErr.ideal.tsig.corruptParties.length + 1 ≤ sErr.ideal.tsig.threshold := by
      rw [hPres.2.1]; exact hDishonest
    obtain ⟨hCust, hMono, hGe, hPair, hHon⟩ :=
      ih hCapErr hCorrErr hDishErr
    rw [hPres.1] at hCust
    rw [hPres.2.2] at hMono hGe
    exact ⟨hCust, hMono, hGe, hPair, hHon⟩

private theorem traceApprovedOutputs_fourLayer {n : Nat} :
    ∀ (tr : List (FourLayerReq n × FourLayerOut)),
      traceApprovedOutputs (tr.map (fun p => (p.1.tx.toTransactionIntent, some p.2.envelope))) =
        tr.map (fun p => p.2.envelope)
  | [] => traceApprovedOutputs_nil
  | _ :: rest => by
    simp only [List.map_cons, traceApprovedOutputs_cons_some, traceApprovedOutputs_fourLayer rest]

/-- **End-to-End Multi-Turn Safety Preservation (`isa_to_ideal_preserves_multiturn_safety`)**:
    Via `ForwardSim.preserve_trace_pred` on `isa_to_mir_to_protocol_to_ideal_sim`, ANY multi-turn
    trace accepted by `layer1CompiledElfMachine` automatically satisfies `FourLayerTraceSafe`
    (cumulative spend `≤ velocityWindowCap`, `Nodup` nonces, strictly increasing epochs, and
    honest validator participation `h ∈ quorum \ corrupt`), AND if `s1Final.cutPoisoned = true`,
    all 32 secret key-share bytes `[0x180, 0x1A0)` in Layer-1 memory are physically `0`! -/
theorem isa_to_ideal_preserves_multiturn_safety {PK : Type} {n q f : Nat}
    (corrupt : List (Fin n)) (pkDigestOf : PK → List UInt8)
    (pk : PK)
    (dealtShares : Nat → Option (List UInt8))
    (custodianShare : List UInt8)
    (signFromShare : List UInt8 → List UInt8 → ByteArray)
    (assembleThresholdSig : (Nat → Option (List UInt8)) → List UInt8 → ByteArray)
    (idealSignOracle : List UInt8 → ByteArray)
    (hBound : n + f < 2 * q)
    (hQPos : 0 < q) (hQLeN : q ≤ n)
    (hCorruptNd : corrupt.Nodup) (hCorruptLe : corrupt.length ≤ f)
    (hSigMatch : ∀ msg : List UInt8, assembleThresholdSig dealtShares msg = signFromShare custodianShare msg)
    (hOracleEq : ∀ msg : List UInt8, assembleThresholdSig dealtShares msg = idealSignOracle msg)
    {s1₀ s1Final : Layer1ElfState}
    {s4₀ : Layer4IdealState PK}
    {trace : List (FourLayerReq n × FourLayerOut)}
    (hRel₀ :
      (isa_to_mir_to_protocol_to_ideal_sim corrupt pkDigestOf pk dealtShares custodianShare
        signFromShare assembleThresholdSig idealSignOracle
        hBound hQPos hQLeN hCorruptNd hCorruptLe hSigMatch hOracleEq).Rel s1₀ s4₀)
    (hTrace1 :
      (layer1CompiledElfMachine q (pkDigestOf pk)
        (fun m msg => signFromShare (readShareMem32 m) msg)).ValidTrace s1₀ trace s1Final) :
    FourLayerTraceSafe s4₀.policy.velocity_window_cap corrupt trace ∧
    (s1Final.cutPoisoned = true →
      ∀ i : Nat, i < 32 → s1Final.mem (UInt64.ofNat 0x180 + UInt64.ofNat i) = 0) := by
  let sim := isa_to_mir_to_protocol_to_ideal_sim corrupt pkDigestOf pk dealtShares custodianShare
    signFromShare assembleThresholdSig idealSignOracle
    hBound hQPos hQLeN hCorruptNd hCorruptLe hSigMatch hOracleEq
  rcases hRel₀ with ⟨s2₀, h12₀, s3₀, h23₀, h34₀⟩
  have hCap₀ : s4₀.policy.accumulated_spend ≤ s4₀.policy.velocity_window_cap := by
    rw [← h34₀.1, ← h23₀.2.1]
    exact h23₀.1
  have hCorr₀ : s4₀.ideal.tsig.corruptParties = corrupt.map Fin.val := by
    rw [← h34₀.2.1]
    exact h23₀.2.2.2.2.2.1.1
  have hDishonest₀ : s4₀.ideal.tsig.corruptParties.length + 1 ≤ s4₀.ideal.tsig.threshold := by
    rw [hCorr₀, List.length_map, ← h34₀.2.1, h23₀.2.2.2.2.1]
    omega
  have hSafe : FourLayerTraceSafe s4₀.policy.velocity_window_cap corrupt trace := by
    apply ForwardSim.preserve_trace_pred sim ⟨s2₀, h12₀, s3₀, h23₀, h34₀⟩ _ hTrace1
    intro tr s4F hTr4
    obtain ⟨hCust, _, _, hEpPair, hHon⟩ :=
      layer4_validTrace_safe corrupt pkDigestOf idealSignOracle hCap₀ hCorr₀ hDishonest₀ hTr4
    have hPolMain := policy_multiturn_velocity_and_intent_binding hCap₀ hCust
    rw [traceApprovedOutputs_fourLayer tr] at hPolMain
    dsimp only at hPolMain
    have hMapAmt :
        ((tr.map (fun p => p.2.envelope)).map (fun e => e.intent.amount_units)) =
          tr.map (fun p => p.2.envelope.intent.amount_units) := by
      rw [List.map_map]; rfl
    have hMapNonce :
        ((tr.map (fun p => p.2.envelope)).map (fun e => e.intent.nonce)) =
          tr.map (fun p => p.2.envelope.intent.nonce) := by
      rw [List.map_map]; rfl
    rw [hMapAmt, hMapNonce] at hPolMain
    exact ⟨hPolMain.2.2.1, hPolMain.2.2.2.1, hEpPair, hHon⟩
  obtain ⟨s4Final, _, s2Final, h12F, _⟩ :=
    sim.lift_validTrace ⟨s2₀, h12₀, s3₀, h23₀, h34₀⟩ hTrace1
  exact ⟨hSafe, sim12_zeroIfPoisoned h12F⟩

/-! ### Multi-Share Shamir Algebra, `#tooth` Session-Gate Refutations & `inhabited_four_layer_chain` -/

/-- Pack 4 canonical `Goldilocks` limbs into a 32-byte big-endian key/share slice. -/
def packLane4Bytes32 (L : Lane4) : List UInt8 :=
  be 8 L.x0.val ++ be 8 L.x1.val ++ be 8 L.x2.val ++ be 8 L.x3.val

theorem packLane4Bytes32_length (L : Lane4) : (packLane4Bytes32 L).length = 32 := by
  unfold packLane4Bytes32
  simp [length_be]

/-- Unpack a 32-byte big-endian key/share slice into a 4-limb `Lane4` element. -/
def unpackLane4Bytes32 (bs : List UInt8) : Lane4 :=
  ⟨Goldilocks.ofNat (ofBE (bs.take 8)),
   Goldilocks.ofNat (ofBE ((bs.drop 8).take 8)),
   Goldilocks.ofNat (ofBE ((bs.drop 16).take 8)),
   Goldilocks.ofNat (ofBE ((bs.drop 24).take 8))⟩

private theorem goldilocks_ofNat_val_eq (x : Goldilocks) : Goldilocks.ofNat x.val = x :=
  Goldilocks.ext (Nat.mod_eq_of_lt x.isLt)

theorem unpackLane4Bytes32_packLane4Bytes32 (L : Lane4) :
    unpackLane4Bytes32 (packLane4Bytes32 L) = L := by
  have hPow : (2 : Nat) ^ 64 = 256 ^ 8 := rfl
  have hTake0 : (packLane4Bytes32 L).take 8 = be 8 L.x0.val := rfl
  have hTake1 : ((packLane4Bytes32 L).drop 8).take 8 = be 8 L.x1.val := rfl
  have hTake2 : ((packLane4Bytes32 L).drop 16).take 8 = be 8 L.x2.val := rfl
  have hTake3 : ((packLane4Bytes32 L).drop 24).take 8 = be 8 L.x3.val := rfl
  unfold unpackLane4Bytes32
  rw [hTake0, hTake1, hTake2, hTake3,
      ofBE_be (hPow ▸ Goldilocks.val_lt_two_pow_64 L.x0),
      ofBE_be (hPow ▸ Goldilocks.val_lt_two_pow_64 L.x1),
      ofBE_be (hPow ▸ Goldilocks.val_lt_two_pow_64 L.x2),
      ofBE_be (hPow ▸ Goldilocks.val_lt_two_pow_64 L.x3),
      goldilocks_ofNat_val_eq, goldilocks_ofNat_val_eq,
      goldilocks_ofNat_val_eq, goldilocks_ofNat_val_eq]

/-- Degree-2 Shamir polynomial $f(x) = \text{sk} + a_1 x + a_2 x^2$ on a single `Goldilocks` coordinate. -/
def shamirEvalCoord (sk a₁ a₂ x : Goldilocks) : Goldilocks :=
  Goldilocks.add sk (Goldilocks.add (Goldilocks.mul a₁ x)
    (Goldilocks.mul a₂ (Goldilocks.mul x x)))

/-- Degree-2 3-of-4 Shamir polynomial evaluation over 4-limb `Lane4` (`256`-bit secret space). -/
def shamirEvalLane4 (sk a₁ a₂ : Lane4) (x : Goldilocks) : Lane4 :=
  ⟨shamirEvalCoord sk.x0 a₁.x0 a₂.x0 x,
   shamirEvalCoord sk.x1 a₁.x1 a₂.x1 x,
   shamirEvalCoord sk.x2 a₁.x2 a₂.x2 x,
   shamirEvalCoord sk.x3 a₁.x3 a₂.x3 x⟩

/-- Non-zero evaluation point $x_p = p + 1 \in \{1, 2, 3, 4\}$ for custodian `p : Fin 4`. -/
def shamirPoint (p : Fin 4) : Goldilocks :=
  Goldilocks.ofNat (p.val + 1)

/-- Multiplicative inverse of $x_p \in \{1, 2, 3, 4\}$ in `Goldilocks`. -/
def shamirPointInv : Fin 4 → Goldilocks
  | ⟨0, _⟩ => Goldilocks.ofNat 1
  | ⟨1, _⟩ => Goldilocks.ofNat 9223372034707292161
  | ⟨2, _⟩ => Goldilocks.ofNat 12297829379609722881
  | ⟨3, _⟩ => Goldilocks.ofNat 13835058052060938241

private theorem shamirPointInv_mul_point (p : Fin 4) :
    Goldilocks.mul (shamirPointInv p) (shamirPoint p) = Goldilocks.one := by
  rcases p with ⟨v, hv⟩
  match v with
  | 0 => dsimp only [shamirPointInv, shamirPoint]; decide
  | 1 => dsimp only [shamirPointInv, shamirPoint]; decide
  | 2 => dsimp only [shamirPointInv, shamirPoint]; decide
  | 3 => dsimp only [shamirPointInv, shamirPoint]; decide
  | n + 4 => omega

/-- Unique degree-1 slope $a_1 = x_p^{-1}(y - (\text{sk} + a_2 x_p^2))$ mapping `sk` to single share `y`. -/
def shamirRecoverSlopeCoord (p : Fin 4) (sk a₂ y : Goldilocks) : Goldilocks :=
  let x := shamirPoint p
  Goldilocks.mul (shamirPointInv p)
    (Goldilocks.sub y (Goldilocks.add sk (Goldilocks.mul a₂ (Goldilocks.mul x x))))

def shamirRecoverSlope (p : Fin 4) (sk a₂ y : Lane4) : Lane4 :=
  ⟨shamirRecoverSlopeCoord p sk.x0 a₂.x0 y.x0,
   shamirRecoverSlopeCoord p sk.x1 a₂.x1 y.x1,
   shamirRecoverSlopeCoord p sk.x2 a₂.x2 y.x2,
   shamirRecoverSlopeCoord p sk.x3 a₂.x3 y.x3⟩

private theorem shamirEval_recover_coord (p : Fin 4) (sk a₂ y : Goldilocks) :
    shamirEvalCoord sk (shamirRecoverSlopeCoord p sk a₂ y) a₂ (shamirPoint p) = y := by
  unfold shamirEvalCoord shamirRecoverSlopeCoord
  dsimp only
  let x := shamirPoint p
  let xInv := shamirPointInv p
  let qTerm := Goldilocks.mul a₂ (Goldilocks.mul x x)
  let diff := Goldilocks.sub y (Goldilocks.add sk qTerm)
  have hCancelX : Goldilocks.mul (Goldilocks.mul xInv diff) x = diff := by
    change CommRingOps.mul (CommRingOps.mul xInv diff) x = diff
    rw [LawfulCommRing.mul_comm xInv diff, LawfulCommRing.mul_assoc]
    change CommRingOps.mul diff (Goldilocks.mul xInv x) = diff
    rw [shamirPointInv_mul_point p]
    exact LawfulCommRing.mul_one diff
  change Goldilocks.add sk (Goldilocks.add (Goldilocks.mul (Goldilocks.mul xInv diff) x) qTerm) = y
  rw [hCancelX]
  dsimp only [diff]
  rw [← goldOfInt_nat sk, ← goldOfInt_nat y, ← goldOfInt_nat qTerm]
  simp only [goldOfInt_add, goldOfInt_sub]
  congr 1
  omega

private theorem shamirRecover_eval_coord (p : Fin 4) (sk a₁ a₂ : Goldilocks) :
    shamirRecoverSlopeCoord p sk a₂ (shamirEvalCoord sk a₁ a₂ (shamirPoint p)) = a₁ := by
  unfold shamirRecoverSlopeCoord shamirEvalCoord
  dsimp only
  let x := shamirPoint p
  let xInv := shamirPointInv p
  let qTerm := Goldilocks.mul a₂ (Goldilocks.mul x x)
  have hSub :
      Goldilocks.sub (Goldilocks.add sk (Goldilocks.add (Goldilocks.mul a₁ x) qTerm))
        (Goldilocks.add sk qTerm) = Goldilocks.mul a₁ x := by
    let lin := Goldilocks.mul a₁ x
    change Goldilocks.sub (Goldilocks.add sk (Goldilocks.add lin qTerm)) (Goldilocks.add sk qTerm) = lin
    rw [← goldOfInt_nat sk, ← goldOfInt_nat lin, ← goldOfInt_nat qTerm]
    simp only [goldOfInt_add, goldOfInt_sub]
    congr 1
    omega
  change Goldilocks.mul xInv
    (Goldilocks.sub (Goldilocks.add sk (Goldilocks.add (Goldilocks.mul a₁ x) qTerm))
      (Goldilocks.add sk qTerm)) = a₁
  rw [hSub]
  change CommRingOps.mul xInv (CommRingOps.mul a₁ x) = a₁
  rw [LawfulCommRing.mul_comm a₁ x, ← LawfulCommRing.mul_assoc]
  change CommRingOps.mul (Goldilocks.mul xInv x) a₁ = a₁
  rw [shamirPointInv_mul_point p]
  exact LawfulCommRing.one_mul a₁

/-- **1-Share Information-Theoretic Independence (`singleShare_uniform_bijection`)**:
    For EVERY custodian `p : Fin 4`, EVERY target secret `sk : Lane4`, and EVERY quadratic mask
    `a₂ : Lane4`, `a₁ ↦ shamirEvalLane4 sk a₁ a₂ (shamirPoint p)` is an explicit constructive
    bijection `Lane4 ≃ Lane4` inverted by `shamirRecoverSlope p sk a₂`: observing any single share
    (such as Layer-1 custodian `1`'s share in `[0x180, 0x1A0)`) reveals zero information about `sk`. -/
theorem singleShare_uniform_bijection (p : Fin 4) (sk a₂ : Lane4) :
    (∀ y : Lane4,
      shamirEvalLane4 sk (shamirRecoverSlope p sk a₂ y) a₂ (shamirPoint p) = y) ∧
    (∀ a₁ : Lane4,
      shamirRecoverSlope p sk a₂ (shamirEvalLane4 sk a₁ a₂ (shamirPoint p)) = a₁) := by
  refine ⟨fun y => ?_, fun a₁ => ?_⟩
  · exact Lane4.ext
      (shamirEval_recover_coord p sk.x0 a₂.x0 y.x0)
      (shamirEval_recover_coord p sk.x1 a₂.x1 y.x1)
      (shamirEval_recover_coord p sk.x2 a₂.x2 y.x2)
      (shamirEval_recover_coord p sk.x3 a₂.x3 y.x3)
  · exact Lane4.ext
      (shamirRecover_eval_coord p sk.x0 a₁.x0 a₂.x0)
      (shamirRecover_eval_coord p sk.x1 a₁.x1 a₂.x1)
      (shamirRecover_eval_coord p sk.x2 a₁.x2 a₂.x2)
      (shamirRecover_eval_coord p sk.x3 a₁.x3 a₂.x3)

/-- Exact Lagrange interpolation at $x = 0$ from quorum `{1, 2, 3}` ($x \in \{2, 3, 4\}$):
    $\lambda_1(0) = 6,\; \lambda_2(0) = -8,\; \lambda_3(0) = 3$. -/
def shamirReconstruct123Coord (y1 y2 y3 : Goldilocks) : Goldilocks :=
  Goldilocks.add
    (Goldilocks.sub (Goldilocks.mul (Goldilocks.ofNat 6) y1)
                    (Goldilocks.mul (Goldilocks.ofNat 8) y2))
    (Goldilocks.mul (Goldilocks.ofNat 3) y3)

def shamirReconstruct123 (sh1 sh2 sh3 : Lane4) : Lane4 :=
  ⟨shamirReconstruct123Coord sh1.x0 sh2.x0 sh3.x0,
   shamirReconstruct123Coord sh1.x1 sh2.x1 sh3.x1,
   shamirReconstruct123Coord sh1.x2 sh2.x2 sh3.x2,
   shamirReconstruct123Coord sh1.x3 sh2.x3 sh3.x3⟩

/-- Exact Lagrange interpolation at $x = 0$ from quorum `{0, 1, 2}` ($x \in \{1, 2, 3\}$):
    $\lambda_0(0) = 3,\; \lambda_1(0) = -3,\; \lambda_2(0) = 1$. -/
def shamirReconstruct012Coord (y0 y1 y2 : Goldilocks) : Goldilocks :=
  Goldilocks.add
    (Goldilocks.sub (Goldilocks.mul (Goldilocks.ofNat 3) y0)
                    (Goldilocks.mul (Goldilocks.ofNat 3) y1))
    y2

def shamirReconstruct012 (sh0 sh1 sh2 : Lane4) : Lane4 :=
  ⟨shamirReconstruct012Coord sh0.x0 sh1.x0 sh2.x0,
   shamirReconstruct012Coord sh0.x1 sh1.x1 sh2.x1,
   shamirReconstruct012Coord sh0.x2 sh1.x2 sh2.x2,
   shamirReconstruct012Coord sh0.x3 sh1.x3 sh2.x3⟩

theorem shamirReconstruct123_correct (sk a₁ a₂ : Lane4) :
    shamirReconstruct123
      (shamirEvalLane4 sk a₁ a₂ (shamirPoint ⟨1, by decide⟩))
      (shamirEvalLane4 sk a₁ a₂ (shamirPoint ⟨2, by decide⟩))
      (shamirEvalLane4 sk a₁ a₂ (shamirPoint ⟨3, by decide⟩)) = sk := by
  have h2 : Goldilocks.ofNat 2 = goldOfInt 2 := by decide
  have h3 : Goldilocks.ofNat 3 = goldOfInt 3 := by decide
  have h4 : Goldilocks.ofNat 4 = goldOfInt 4 := by decide
  have h6 : Goldilocks.ofNat 6 = goldOfInt 6 := by decide
  have h8 : Goldilocks.ofNat 8 = goldOfInt 8 := by decide
  have hCoord : ∀ s b1 b2 : Goldilocks,
      shamirReconstruct123Coord
        (shamirEvalCoord s b1 b2 (Goldilocks.ofNat 2))
        (shamirEvalCoord s b1 b2 (Goldilocks.ofNat 3))
        (shamirEvalCoord s b1 b2 (Goldilocks.ofNat 4)) = s := by
    intro s b1 b2
    unfold shamirReconstruct123Coord shamirEvalCoord
    rw [h2, h3, h4, h6, h8, ← goldOfInt_nat s, ← goldOfInt_nat b1, ← goldOfInt_nat b2]
    simp only [goldOfInt_add, goldOfInt_sub, goldOfInt_mul]
    congr 1
    omega
  exact Lane4.ext
    (hCoord sk.x0 a₁.x0 a₂.x0)
    (hCoord sk.x1 a₁.x1 a₂.x1)
    (hCoord sk.x2 a₁.x2 a₂.x2)
    (hCoord sk.x3 a₁.x3 a₂.x3)

