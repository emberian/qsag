module

public import Qsag.Machine.ElfFunctionalEquiv.ScalarAndArchive
public import Qsag.Machine.ElfFunctionalEquiv.SimdAndScalarKernels
public import Qsag.Machine.ElfFunctionalEquiv.GfniShamir
public import Qsag.Machine.ElfFunctionalEquiv.KeccakMpcAndThetaRho
public import Qsag.Machine.ElfFunctionalEquiv.Keccak4xEquiv
public import Qsag.Machine.ElfFunctionalEquiv.Gf128PclmulX86
public import Qsag.Machine.ElfFunctionalEquiv.Gf128ArmAndTower
import Qsag.Tactic.AssuranceKit

/-!
# Compiled-Byte Machine-Code Functional Equivalence & Unified CT-NI Certificates (`ElfFunctionalEquiv.lean`)

Lean 4.35 functional equivalence layer for selected historical and current compiled `.rlib` / `ELF64`
machine-code byte slices (`CompiledRlibFixtures.lean`, `ElfParse.lean`, `ElfBinaryVerify.lean`)
to canonical mathematical and cryptographic specifications (`Goldilocks.lean`, `BinaryTower.lean`,
`Keccak.lean`, `ConstantTimeIsa.lean`).
The original scalar group covers 12 kernels. The imported SIMD, field and Keccak
proofs extend functional coverage to 26 distinct archive symbols.
The historical declarations retain frozen challenge bindings; complete functional coverage
for all 28 live kernels remains open. Freshness is checked independently by the ELF auditor.
-/

public section

namespace Qsag

set_option autoImplicit false

/-- The decoded production `pclmul` kernel run, read in the tower basis: the output block is the
    initial accumulator plus the `Tower128` dot product of the input blocks. -/
theorem current_rlib_gf2_128_mul_acc_pclmul_tower_dot
    (s : X86State) (k extra : Nat) (hk : k+1 < 2^64) (hp : s.pc = 0)
    (hh : s.halted = false) (hn : s.gpr.r1 = UInt64.ofNat (k+1)) :
    polyToTower128 (gf128Words
        (readMem64 (runX86 gf128PclmulProg (34 + 16*(k+1) + extra) s).1.mem s.gpr.r7)
        (readMem64 (runX86 gf128PclmulProg (34 + 16*(k+1) + extra) s).1.mem (s.gpr.r7+8))) =
      towerAdd 7
        (polyToTower128 (gf128Words (readMem64 s.mem s.gpr.r7) (readMem64 s.mem (s.gpr.r7+8))))
        (gf128PclmulTowerSum (k+1) s.mem s.gpr.r6 s.gpr.r2) := by
  obtain ⟨_, _, _, _, hout, _⟩ := current_rlib_gf2_128_mul_acc_pclmul_functional s k extra hk hp hh hn
  rw [hout, polyToTower128_xor, polyToTower128_gf128PclmulFieldSum]

/-- The decoded production `vpclmulqdq` kernel run, read in the tower basis. -/
theorem current_rlib_gf2_128_mul_acc_vpclmul_tower_dot
    (s : X86State) (k extra : Nat) (hk : k+1 < 2^64) (hp : s.pc = 0)
    (hh : s.halted = false) (hn : s.gpr.r1 = UInt64.ofNat (k+1)) :
    polyToTower128 (gf128Words
        (readMem64 (runX86 gf128VpclmulProg (40 + 16*(k+1) + extra) s).1.mem s.gpr.r7)
        (readMem64 (runX86 gf128VpclmulProg (40 + 16*(k+1) + extra) s).1.mem (s.gpr.r7+8))) =
      towerAdd 7
        (polyToTower128 (gf128Words (readMem64 s.mem s.gpr.r7) (readMem64 s.mem (s.gpr.r7+8))))
        (gf128VpclmulTowerSum (k+1) s.mem s.gpr.r6 s.gpr.r2) := by
  obtain ⟨_, _, _, _, hout, _⟩ := current_rlib_gf2_128_mul_acc_vpclmul_functional s k extra hk hp hh hn
  rw [hout, polyToTower128_xor, polyToTower128_gf128VpclmulFieldSum]

#verify_constructive current_rlib_gf2_128_mul_acc_pclmul_tower_dot
#verify_constructive current_rlib_gf2_128_mul_acc_vpclmul_tower_dot

end Qsag
end
