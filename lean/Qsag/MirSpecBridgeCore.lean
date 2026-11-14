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
import all Qsag.RssSlhFullSecurity
import all Qsag.CustodySuiteFull
import all Qsag.ElfBinaryVerify
import all Qsag.ElfParse
import all Qsag.ThresholdMlDsaAndToprf

/-!
# Qsag.MirSpecBridge — fixed-width guard models and their composition into the protocol specs

## What this file is and is not

Every `Mir*` structure and machine in this file is a **hand-written Lean model**. The `qsag`
package does not import the Aeneas extraction (`aeneas/lean`, package `qsag_aeneas`), so no
declaration here mentions `QsagVerified.Funs`, and no theorem here is about extracted Rust MIR.
The dependency runs the other way: `qsag_aeneas` requires `qsag`, and
`aeneas/lean/QsagVerified/Proofs/AuthenticatedBeltAndRealSpecWeld.lean` imports both the
extraction and this module and proves the links that exist. Per model:

| Model here | Linked to the Aeneas extraction? |
|---|---|
| `MirRssCutSession` / `mirRssCutMachine` (§3) | Yes: `extractedRssCut_forwardSim_mirRssCut`, a lockstep forward simulation from the extracted `rss_cut_session.RssCutGateSession.step`. |
| `MirPolicyGuardState` (§2) | No. It is a `UInt64` burned-nonce design; the extracted `StatefulVelocityGuard` is a `u128` monotonic-nonce design and production `crates/qsag-policy` is a third. |
| `MirRssMlDsaKeyState` and the ML-DSA gate (§3) | No. The extracted `MlDsaReleaseGate` takes four caller booleans; this model computes norms. |
| `MirBeltLatchState` (§4) | No. Field-for-field `WalLatchState`; the extracted guard is `VerifiedBeltQuorumGuard`. |
| `Layer1ElfState`, `Layer2MirState` and the four-layer chain (§5) | Layer 1 runs decoded machine code through `McRefine`. Layer 2 is a model that evaluates the pre-cut transcript predicate itself and is not extracted. |

Names keep their `Mir` prefix because other modules and documents refer to them; read it as
"model at MIR granularity", not "derived from MIR".

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

5. **§5. Four-layer conditional refinement chain (`isa_to_mir_to_protocol_to_ideal_sim`).**
   Conditional control-flow and authorization `ForwardSim.trans` across the decoded ELF slice,
   the Layer-2 guard model, the three-round interactive protocol, and the share-free Layer-4 guard
   state (parameterized at the cryptographic signing boundary by `hSigMatch` and `hOracleEq`),
   enforcing session-bound stored width-12 `Poseidon2` Round-1 commitments, verifier-held `BGIN19`
   MAC keys, and `§4`-authenticated quorum certificates, paired with a Shamir multi-share 2-turn
   execution witness and `#tooth` regressions. "MIR" in the theorem name refers to the Layer-2 model.

Constructive throughout: no proof gaps, no custom axioms, no `Classical.choice`.
-/

public section

namespace Qsag

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
