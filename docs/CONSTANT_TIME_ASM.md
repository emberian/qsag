# `qsag-asm` & `Qsag.Machine`: Platform SIMD Assembly, Formal Machine-Code Noninterference, and Empirical Timing Verification

This document specifies **Pillar 3** of qsag — Quorum-Switching AGgregation / Quantum Succinct AGgregation:

1. **`crates/qsag-asm`**: Zero-dependency `#![no_std]` crate with 19 `x86_64` and 9 `aarch64` hand-written assembly kernels (`AVX2`, `GFNI`, `VPCLMULQDQ`/`PCLMULQDQ`, `BMI2`/`ADX`; `ARMv8.2-SHA3`, `PMULL`, `NEON`, `ARMv8.4-DIT`), compiled-Rust SIMD modules for `AVX-512`, `SHA-NI`, `vpshufb` and `NEON` (Section 2.3), runtime `CPUID`/`XGETBV`/`AT_HWCAP`/`sysctlbyname` capability probing across five backend tiers, and a branchless portable fallback with no secret-indexed table.
2. **`scripts/audit_elf_ct.py`**: Automated static binary disassembly verifier auditing every required assembly symbol and selected compiled Rust SIMD/wipe functions in native `.o` or `.rlib`, and both Linux ELF and Apple Mach-O `aarch64` assembly kernels, with negative `#tooth` self-tests. `crates/qsag-asm/scripts/audit_elf_ct.py` is a seven-line compatibility entry point that runs the repository-root script.
3. **`lean/Qsag/Machine/`**: Lean 4.35 leakage semantics and taint-noninterference checkers (`0 sorry`, `0 axiom`, `0 native_decide`). `ConstantTimeIsa.lean` is the checker over a hand-written instruction AST and models no `qsag-asm` kernel; the kernels are proved on their **decoded bytes** in `IsaCt.lean`, `ElfVerify.lean`, `ElfFixtureVerify.lean`, `McRefine.lean`, `ElfFunctionalEquiv.lean`, `SydTv.lean` and `ClmulSimd.lean` (Section 6).
4. **`crates/qsag-asm/{examples,tests}/ct_dudect.rs`**: Empirical Welch's $t$-test constant-time harness (`1,000,192` cycle-counter traces per kernel in deep mode; `25,600`-trace sub-second CI gate via `QSAG_DUDECT_SAMPLES`), validated on both **Intel Core i9-12900 (`Alder Lake`, `AVX2+GFNI+VPCLMULQDQ`)** and **AMD EPYC-Milan (`Zen 3`, `AVX2+PCLMULQDQ`)**.

Lean noninterference certificates cover all 28 assembly symbols of the two fixture archives
(19 `x86_64`, 9 `aarch64`; 1,935 + 1,420 = 3,355 decoded instructions) under the modeled leakage
semantics. Functional coverage remains kernel-specific. `ElfFunctionalEquiv.lean` now includes
`current_rlib_keccak_f1600_avx2_4x_functional` for the full four-lane, 24-round permutation;
its older header count of 12 kernels is not a current inventory. The seven triangles in
`aeneas/lean/QsagVerified/Proofs/ElfMirTriangles.lean` connect selected archive symbols to
extracted MIR through canonical specifications, under entry/frame conditions. These results
do not establish complete functional coverage of all 28 symbols or the whole BDOZ protocol. The compiled-Rust SIMD modules of
Section 2.3 have no Lean certificate. See [binary verification](BINARY_RLIB_VERIFICATION.md)
for fixture binding.

The binary auditor covers the 16 x86 kernels of `x86_64_asm.rs` (ELF, Windows COFF, Apple
Mach-O), the 7 AArch64 kernels of `aarch64_kernels.s` / `aarch64_asm.rs` (ELF and Mach-O), the
5 `bitslice.rs` kernels (3 x86, 2 AArch64; in the compiled ELF, and the two AArch64 bodies by
cross-assembly), and emitted Rust crypto functions: 19 x86-64 and 9 AArch64 assembly symbols
in all. Compiled Rust checks select the `target_feature` SIMD entries, bitslice/linear-map functions
and wipe helpers for control-flow/dataflow screening. Other compiled Rust functions are
counted and reported without being checked. This is not a whole-program taint proof. The empirical harness exercises **10 dispatched
operations**, including `qsag_asm_goldilocks_mul_ct`; backend selection determines which
assembly implementation runs. A passing timing sample is evidence, not universal timing proof.

---

## Grounded ISA integration and scope

`ConstantTimeIsa.lean`, `IsaCt.lean`, `ElfVerify.lean` and `ElfFixtureVerify.lean` are the ISA/ELF pillar alongside
protocol/UC/POSIX/QROM proofs and compiler-extracted MIR. LNSym / x86lean /
ELFSage semantic grounding, linked ThinLTO coverage and physical x86_64
`lake exe isa-cosim` are active integration work. Existing checker/model proofs
must not be described as already validating every real instruction and dispatch path.
The live `qsag-asm` implementation includes 256-lane Keccak and carryless
PCLMULQDQ/VPCLMULQDQ/PMULL kernels used by Pants signing and BGIN19 DZK.

DOIT and aarch64 **PSTATE.DIT** are explicit runtime assumptions; feature detection
alone does not prove an operating mode is enabled. Scratch-register zero-on-exit
and `#tooth` byte mutations apply to the checked kernels and their frame contracts.
They do not erase caller frames, preserved registers, compiler copies or OS saves.
A call is not a scrub; `vzeroupper` clears upper state, not every vector secret.
Higher-level rustc/LLVM, wrappers and reachable fallbacks remain in the leakage TCB.
Speculation, SMT/cache effects outside the observation model and physical faults
are not covered by architectural taint noninterference.

**Verify your code, test your specs:** `spec-oracle` differential/clause-drop tests,
native `isa-cosim`, `ct_dudect` and six-kernel `comparator --paranoid` CI replay
supply complementary evidence. Recorded timing tables below are historical samples,
not a universal guarantee or a fresh test of the current checkout. Linked-binary
coverage and mandatory CI dependencies must be established for each release.
See [ASSURANCE.md](../ASSURANCE.md) for the complete boundary.

## 1. Microarchitectural Leakage Model & Constant-Time Discipline

The implementation is designed around the following disciplines. The Lean proofs establish them for the modeled programs under the stated leakage model; binary audits and timing tests provide separate evidence for other kernels.

1. **Public Control Flow (`PC` Invariance):**
   - Checked kernels require secret-independent conditional branches (`jcc`, `cbz`, `cbnz`, `tbz`, `tbnz`); source-wide and dispatch coverage require separate evidence.
   - Loop back-edges depend exclusively on public slice-length trip counts (`blocks`, `count`, `len`).
2. **Public Memory Access Trace (Cache-Line & Bank Invariance):**
   - No memory address depends on a secret: there is no secret-indexed load (`[base + secret * scale]`, `vpgather*`, or a pointer formed by adding a secret) in the assembly kernels or the portable fallback.
   - Secret-indexed *register* lookups are used and are constant time: `vpshufb` (`gf256_simd.rs`) and `tbl` / `vqtbl1q_u8` (`aarch64_simd.rs`) select a byte of a 16-byte table that is already in a vector register, by a secret nibble. The instruction touches no memory, so the cache trace is unchanged; this is the $\mathcal{T}_3 \cong \mathbb{F}_{2^8}$ Shamir path on CPUs without GFNI.
   - The crate does contain static constant tables, read only at public offsets (Section 3.3): the four `ByteMatrices` statics of `linear_map.rs` (2 KiB each, 64-byte aligned), the 4 KiB `T7_TO_POLY_SELECTORS` of `lib.rs`, the two 128-entry `u128` basis arrays `T7_TO_POLY_BASIS` / `POLY_TO_T7_BASIS` of `portable.rs`, and `T3_VPSHUFB_CONSTS`. Earlier revisions of this document described the $\mathcal{T}_7$ basis change as using zero static tables; that is not what the code does.
3. **Fixed-Latency Operand Discipline & Hardware `DIT` / `DOITM`:**
   - The instruction rules reject variable-latency integer dividers (`div`, `idiv`, `udiv`, `sdiv`) and secret-count variable shifts in audited paths. This does not establish coverage of every compiled Rust routine.
   - Conditional data selection uses pure fixed-latency ALU carry/borrow masks (`sbb reg, reg` on `x86_64`; `sbc reg, xzr, xzr` / `adc reg, xzr, xzr` + `neg` on `aarch64` — avoiding `cmovcc`, `csel`, `cset`, and `csetm` when hardware DIT is inactive).
   - `enable_hardware_dit()` (`crates/qsag-asm/src/cpuid.rs`) executes `msr dit, #1` (`PSTATE.DIT = 1`) in EL0 userspace **only** after verifying runtime `AT_HWCAP` (`HWCAP_DIT = 1 << 24` on Linux) or `sysctlbyname("hw.optional.arm.FEAT_DIT")` on Apple Silicon (preventing `SIGILL` on pre-ARMv8.4 cores). On `x86_64`, `CPUID.(EAX=7,ECX=0):EDX[29]` (read from `__cpuid_count(7, 0)` in `cpuid.rs`) enumerates `IA32_ARCH_CAPABILITIES` MSR presence (`x86_arch_capabilities_msr`), while `x86_doit_enumerated` remains `false` in unprivileged ring-3 because `IA32_ARCH_CAPABILITIES[12]` (`DOITM`) and `IA32_UARCH_MISC_CTL[0]` require ring-0 `RDMSR`/`WRMSR`.
4. **Architectural & Scratch Zeroization:**
   - Every `AVX2` kernel wipes scratch `ymm` registers via `vpxor ymm, ymm, ymm` and executes `vzeroupper` prior to `ret` (preventing dirty upper-YMM AVX$\leftrightarrow$SSE transition penalties and residual secret state in touched SIMD scratch registers).
   - Every `aarch64` NEON/SHA3/PMULL kernel (both Linux ELF `src/asm/aarch64_kernels.s` and Apple Mach-O `src/aarch64_asm.rs`) preserves AAPCS64 callee-saved `d8..d15` (saving/restoring full 128-bit `q8..q15` where needed) and explicitly wipes touched caller-saved vector registers via `eor vN.16b, vN.16b, vN.16b` before `ret`.
   - The compiled-Rust NEON kernels of `aarch64_simd.rs` end with `wipe_neon_scratch_regs`, an inline-assembly block that zeroes all 24 AAPCS64 caller-saved vector registers, `v0..v7` and `v16..v31`, and declares each as an `out` clobber. `v8..v15` are callee-saved in their low 64 bits and are left to the compiler epilogue. `scripts/audit_elf_ct.py` tracks the same 24 registers live at `ret` for compiled SIMD kernels and carries self-tests for an unwiped `v24` and for `ld4` / `ld1` range loads into `v24..v31`.
   - Temporary stack buffers holding secret shares or basis-converted field elements (`b0`, `b1`, `chunk_poly`, `poly_acc*`) are wiped via `ct_memzero` / `core::ptr::write_volatile` before scope exit.

---

## 2. Cross-Platform ABI & Runtime Dispatch Architecture

### 2.1 Explicit `extern "sysv64"` Calling Convention (`x86_64`)

All 19 `x86_64` `global_asm!` kernels (16 in `crates/qsag-asm/src/x86_64_asm.rs`, 3 in `crates/qsag-asm/src/bitslice.rs`) follow the System V AMD64 register convention (`rdi, rsi, rdx, rcx, r8, r9`; `rbx, rbp, r12..r15` callee-saved). Every `x86_64` FFI declaration in `x86_64_asm.rs` and `bitslice.rs` is in an `unsafe extern "sysv64"` block rather than `extern "C"` (the `aarch64` declarations use `extern "C"`), guaranteeing that on `x86_64-pc-windows-msvc` / `x86_64-pc-windows-gnu` LLVM automatically bridges Windows x64 arguments (`rcx, rdx, r8, r9`) and preserves Windows non-volatile registers (`rdi, rsi, xmm6..xmm15`). The Keccak scratch frame is explicitly aligned to 32 bytes; entry/return stack alignment follows the calling convention. These global kernels avoid red-zone (`[rsp - disp]`) accesses.

### 2.2 Lock-Free Runtime Backend Selection

`detect_backend()` (`crates/qsag-asm/src/cpuid.rs`) caches one of five `SimdBackend` tiers in an `AtomicU8`. `backend_for_capabilities` tests them in the order of the table and takes the first whose requirements hold:

| `SimdBackend` Tier (discriminant) | Target ISA & Required Extensions | Verified Host |
| :--- | :--- | :--- |
| `X86Avx512GfniVpclmul` (5) | `x86_64` + `AVX-512` (`F` + `DQ` + `BW` + `VL`, OS `XCR0[7:5]=111b`) + `AVX2` + `BMI1` + `BMI2` + `ADX` + `GFNI` + `VPCLMULQDQ` | No timing table is recorded in this document for this tier |
| `X86Avx2GfniVpclmul` (3) | `x86_64` + OS `XGETBV(XCR0[2:1]=11b)` + `AVX2` + `BMI1` + `BMI2` + `ADX` + `GFNI` + `VPCLMULQDQ` | Intel Core i9-12900 (Alder Lake) |
| `X86Avx2Pclmul` (2) | `x86_64` + OS `XGETBV(XCR0[2:1]=11b)` + `AVX2` + `BMI1` + `BMI2` + `ADX` + `PCLMULQDQ` | AMD EPYC-Milan (Zen 3) |
| `Aarch64NeonSha3Pmull` (4) | `aarch64` + `AdvSIMD` + `FEAT_SHA3` (`eor3`/`rax1`/`xar`/`bcax`) + `FEAT_PMULL` | Linux `AT_HWCAP` / Apple `sysctlbyname` |
| `Portable` (1) | Pure `#![no_std]` branchless Rust with no secret-indexed table and no `cl` shift | All targets (`cargo test` cross-tier parity) |

`FEAT_DIT` is not a tier requirement: `Aarch64NeonSha3Pmull` is selected with or without it
(`arm_acceleration_does_not_require_optional_dit`), and DIT is enabled separately when present.
Several kernels are additionally gated on individual capability bits at the call site, so a
tier names the widest path that may run, not the path that does (for example the AVX-512 tier
runs `avx512::gf256_shamir_*_avx512_gfni` on 64-byte blocks and the GFNI assembly on the rest).

### 2.3 Kernel and Module Inventory

**Hand-written assembly: 19 `x86_64` symbols.**

| Source | Symbols |
| :--- | :--- |
| `src/x86_64_asm.rs` (16) | `qsag_asm_keccak_f1600_avx2_4x`, `qsag_asm_keccak_chi_mpc_avx2`, `qsag_asm_gf256_shamir_mul_gfni`, `qsag_asm_gf256_shamir_mac_gfni`, `qsag_asm_gf256_shamir_mul_avx2`, `qsag_asm_gf256_shamir_mac_avx2`, `qsag_asm_tower128_bdoz_mac_vpclmul`, `qsag_asm_tower128_bdoz_mac_pclmul`, `qsag_asm_goldilocks_mul_ct_x86_64`, `qsag_asm_goldilocks_add_ct_x86_64`, `qsag_asm_goldilocks_sub_ct_x86_64`, `qsag_asm_goldilocks_pow7_ct_x86_64`, `qsag_asm_goldilocks_dot2_adx_x86_64`, `qsag_asm_ct_eq_32_x86_64`, `qsag_asm_ct_eq_bytes_x86_64`, `qsag_asm_ct_memzero_x86_64` |
| `src/bitslice.rs` (3; transpose body in `src/asm/x86_64_transpose64x256.s`) | `qsag_asm_transpose64x256_avx2`, `qsag_asm_gf2_128_mul_acc_pclmul`, `qsag_asm_gf2_128_mul_acc_vpclmul` |

**Hand-written assembly: 9 `aarch64` symbols.**

| Source | Symbols |
| :--- | :--- |
| `src/asm/aarch64_kernels.s` (Linux ELF) and the inline copy in `src/aarch64_asm.rs` (Apple Mach-O, `_`-prefixed) (7) | `qsag_asm_enable_dit_aarch64`, `qsag_asm_keccak_sha3_neon`, `qsag_asm_keccak_theta_rho_sha3_neon`, `qsag_asm_tower128_bdoz_mac_pmull`, `qsag_asm_goldilocks_mul_ct_aarch64`, `qsag_asm_ct_eq_32_aarch64`, `qsag_asm_ct_memzero_aarch64` |
| `src/bitslice.rs` (2; transpose body in `src/asm/aarch64_transpose64x256.s`) | `qsag_asm_transpose64x256_neon`, `qsag_asm_gf2_128_mul_acc_pmull` |

These 28 symbols are the ones named by `currentX86SymbolContracts` and
`currentAarch64SymbolContracts` in `lean/Qsag/Machine/ElfVerify.lean`.

**Compiled Rust SIMD modules.** These are Rust `#[target_feature]` functions using intrinsics and, in some modules
such as `gf256_simd.rs`, inline assembly. They are compiled by rustc/LLVM, so their machine code is covered by the
instruction-rule audit of the release archive (`REQUIRED_SIMD_SYMBOLS` in
`scripts/audit_elf_ct.py` names each entry point so that a missing kernel fails the audit) and
not by the Lean symbol contracts above.

| Module | Target | Entry points |
| :--- | :--- | :--- |
| `src/avx512.rs` | `x86_64` | `keccak_f1600_avx512_8x`, `gf256_shamir_mul_avx512_gfni`, `gf256_shamir_mac_avx512_gfni`, `tower128_bdoz_mac_avx512_evex`, `gf2_128_mul_acc_avx512_evex`, `poly_scale_xor_avx512_evex` |
| `src/gf256_simd.rs` | `x86_64` | `gf256_shamir_mul_vpshufb_avx2`, `gf256_shamir_mac_vpshufb_avx2_x1`, `gf256_shamir_mac_4vpshufb_avx2_x2` |
| `src/linear_map.rs` | `x86_64`, `aarch64` | `gfni128`, `gfni512`, `gfni512x8`, `pclmul_map`, `pmull_map` (the $\mathcal{T}_7$ basis change) |
| `src/ntt_simd.rs` | `x86_64` | `mldsa_ntt_avx2`, `mldsa_ntt_avx512`, `mldsa_inv_ntt_avx2`, `mldsa_inv_ntt_avx512`, `mldsa_pointwise_mul_avx2`, `mldsa_pointwise_mul_avx512`, with portable `mldsa_ntt_portable`, `mldsa_inv_ntt_portable`, `mldsa_pointwise_mul_portable` |
| `src/sha2_hw.rs` | `x86_64`, `aarch64` | `sha256_compress_blocks_shani`, `sha256_compress_blocks_aarch64_sha2`, with `sha256_compress_blocks_portable` |
| `src/aarch64_simd.rs` | `aarch64` | `gf256_shamir_mul_pmull_neon`, `gf256_shamir_mac_pmull_neon`, `keccak_chi_mpc_row256_neon`, `mldsa_ntt_neon`, `mldsa_inv_ntt_neon`, `mldsa_pointwise_mul_neon` |

`src/bitslice.rs` also holds the Rust dispatchers and portable versions around its five
assembly kernels (`transpose64x256`, `gf2_128_mul_acc_batch`, `gf2_128_scale_xor`,
`gf2_128_dot`, `gf2_64x128_clmul_acc`, `gf2_xor_combine_planes`); `src/portable.rs` is the
fallback for every operation; `src/wipe.rs` and `src/durable.rs` hold register and memory
wiping and durable-storage helpers.

Both `src/asm/aarch64_kernels.s` and `src/aarch64_asm.rs` emit `.arch armv8.4-a+sha3+crypto` inside the assembly translation unit so baseline `aarch64-unknown-linux-gnu` builds compile cleanly without global `-C target-feature` flags while guarding execution behind runtime `AT_HWCAP` / `sysctlbyname` checks.

---

## 3. Algebraic Basis Isomorphisms & Kernel Designs

### 3.1 4-Way Parallel `Keccak-f[1600]` & 256-Way Bitsliced 3-Party RSS MPC $\chi$

- **`qsag_asm_keccak_f1600_avx2_4x` (`x86_64` AVX2):** Evaluates 4 independent 1600-bit sponges (`25 × u64 × 4` lanes = `800 B` interleaved as 25 groups of four lanes) across all 24 rounds, computing $\theta, \rho, \pi, \chi$ (`vpandn + vpxor`), and $\iota$. Each round reads and rewrites the 800-byte state in memory and uses 800 bytes of aligned stack scratch inside an 832-byte allocation; the scratch is wiped before return.
- **`qsag_asm_keccak_chi_mpc_avx2` (`x86_64` AVX2):** Processes **256 parallel Keccak $\chi$-rows simultaneously** (`4 × 64` bits per `YMM`) under 3-party Replicated Secret Sharing (RSS):
  $$z_i^{(x)} = s_i^{(x)} \oplus \bigl(\neg s_i^{(x+1)} \land s_i^{(x+2)}\bigr) \oplus \bigl(s_i^{(x+1)} \land t_i^{(x+2)}\bigr) \oplus \bigl(t_i^{(x+1)} \land s_i^{(x+2)}\bigr) \oplus m_i^{(x)}$$
  satisfying $\bigoplus_{p \in \{0,1,2\}} z^{(p)} = a \oplus (\neg b \land c)$ for all $a = \bigoplus_p s^{(p)},\; b = \bigoplus_p s^{(p)}_{+1},\; c = \bigoplus_p s^{(p)}_{+2}$ when each party holds the adjacent replicated share $t_i = s_{i+1}$ (indices modulo 3) and $m^{(0)} \oplus m^{(1)} \oplus m^{(2)} = 0$.
- **`qsag_asm_keccak_sha3_neon` & `qsag_asm_keccak_theta_rho_sha3_neon` (`aarch64` `FEAT_SHA3`):** Executes native 2-way 64-bit SIMD `eor3.16b`, `rax1.2d`, `xar.2d`, and `bcax.16b` (`d = a ^ (b & ~c)`), wired directly into `keccak_f1600_x4_with_backend` under `SimdBackend::Aarch64NeonSha3Pmull`.

### 3.2 Wiedemann Tower $\mathcal{T}_3 \cong \mathbb{F}_{2^8}$ Shamir Kernels (`GFNI` & `AVX2`)

`QSAG` represents $\mathbb{F}_{2^8}$ via the Wiedemann tower $\mathcal{T}_0 = \mathbb{F}_2$, $\mathcal{T}_1 = \mathcal{T}_0[x_0]/(x_0^2 + x_0 + 1)$, $\mathcal{T}_2 = \mathcal{T}_1[x_1]/(x_1^2 + x_0 x_1 + 1)$, $\mathcal{T}_3 = \mathcal{T}_2[x_2]/(x_2^2 + x_1 x_2 + 1)$, whereas Intel `VGF2P8MULB` multiplies in the AES polynomial basis $\mathbb{F}_2[z]/(z^8 + z^4 + z^3 + z + 1)$ (`0x11B`).

Mapping the tower generators $(1, x_0, x_1, x_0 x_1, x_2, x_0 x_2, x_1 x_2, x_0 x_1 x_2)$ to roots in $\mathbb{F}_2[z]/(z^8 + z^4 + z^3 + z + 1)$:
- $\phi(x_0) = \text{0xBC}$ ($\phi(x_0)^2 \oplus \phi(x_0) = 1$),
- $\phi(x_1) = \text{0xB0}$ ($\phi(x_1)^2 \oplus \phi(x_0)\phi(x_1) = 1$),
- $\phi(x_2) = \text{0x63}$ ($\phi(x_2)^2 \oplus \phi(x_1)\phi(x_2) = 1$).

yields the exact `VGF2P8AFFINEQB` $8\times 8$ bit-matrices (packed MSB-first per `VGF2P8AFFINEQB` lane semantics):
- tower-to-polynomial immediate `0x71500A8A86BE78CE` ($\phi : \mathcal{T}_3 \xrightarrow{\sim} \mathbb{F}_2[z]/(z^8 + z^4 + z^3 + z + 1)$)
- polynomial-to-tower immediate ` 0xA1E4F8E072A2700C` ($\phi^{-1} : \mathbb{F}_2[z]/(z^8 + z^4 + z^3 + z + 1) \xrightarrow{\sim} \mathcal{T}_3$)

`qsag_asm_gf256_shamir_mul_gfni` and `qsag_asm_gf256_shamir_mac_gfni` evaluate **32 parallel $\mathcal{T}_3$ multiplications per `YMM` vector** via $\phi^{-1}(\phi(a) \cdot_{\text{0x11B}} \phi(b))$ (with $\phi$ lifted out of the inner loop in `mac_gfni`).

**Dispatch (`gf256_shamir_mul_with_backend`, `gf256_shamir_mac_with_backend` in `src/lib.rs`).** The first applicable branch runs:

| Condition | `mul` | `mac` |
| :--- | :--- | :--- |
| `X86Avx512GfniVpclmul` with `avx512` and `gfni` | `avx512::gf256_shamir_mul_avx512_gfni` on 64-byte blocks | `avx512::gf256_shamir_mac_avx512_gfni` on 64-byte blocks |
| `X86Avx2GfniVpclmul` or `X86Avx512GfniVpclmul` with `avx2` and `gfni` | `qsag_asm_gf256_shamir_mul_gfni` (32-byte blocks) | `qsag_asm_gf256_shamir_mac_gfni` (32-byte blocks) |
| any `x86_64` tier with `avx2` (no GFNI, e.g. Zen 3) | `gf256_simd::gf256_shamir_mul_vpshufb_avx2` | `gf256_simd::gf256_shamir_mac_4vpshufb_avx2_x2` on 64-byte blocks, `gf256_simd::gf256_shamir_mac_vpshufb_avx2_x1` on the 32-byte remainder |
| `Aarch64NeonSha3Pmull` | `aarch64_simd::gf256_shamir_mul_pmull_neon` | `aarch64_simd::gf256_shamir_mac_pmull_neon` |
| otherwise | `portable::gf256_shamir_mul_portable` | `portable::gf256_shamir_mac_portable` |

The non-GFNI path is therefore the compiled-Rust `vpshufb` module, **not** the assembly
kernels `qsag_asm_gf256_shamir_mul_avx2` / `qsag_asm_gf256_shamir_mac_avx2`. Those two
assembly kernels implement an 8-stage Russian-peasant shift-and-XOR chain; they remain in the
archive and in the audited and Lean-contracted symbol set, but the dispatcher never selects
them. They are reachable only through the explicit wrappers
`gf256_shamir_mul_avx2_russian_peasant` and `gf256_shamir_mac_avx2_russian_peasant`.

`gf256_simd.rs` works in the tower directly. A byte $a = a_0 + a_1\alpha \in \mathcal{T}_3$ splits into two nibbles in $\mathcal{T}_2 = \mathbb{F}_{16}$; since $\mathcal{T}_2^\times \cong C_{15}$, its logarithm and exponential tables are 16 bytes each and fit one `vpshufb` lane. The constants (`T3_VPSHUFB_CONSTS`) are loaded into `ymm` registers once per call; each `vpshufb` then indexes a register by a secret nibble and reads no memory. Setting `LOG_T2[0] = 0x80` with saturating `vpaddusb` makes bit 7 flag a zero operand, so `vpshufb` zeroes the product without a branch. A `const` block checks all $16 \times 16 = 256$ nibble pairs for the modeled table instructions against `tower_mul_t2` and the scaled product. Full $256 \times 256$ byte-pair parity is a separate runtime test, not this compile-time check. On `aarch64` the same split-nibble method uses `vqtbl1q_u8` (`tbl`) with `vmull_p8` (`PMULL`).

Recorded throughput speedups over the portable code are **505.2×** (`mul`) and **517.0×** (`mac`) on the GFNI path (Intel Core i9-12900) and **51.3×** (`mul`) and **365.0×** (`mac`) on the non-GFNI AVX2 path (AMD EPYC-Milan). These are historical measurements (Section 5.3); they have not been re-taken against the current dispatch.

### 3.3 2-Lane $\mathbb{F}_{2^{128}}$ BDOZ MAC (`VPCLMULQDQ` / `PCLMULQDQ` / `PMULL`) & $\mathcal{T}_7$ Basis Change

- **Polynomial-Basis Inner Product (`qsag_asm_tower128_bdoz_mac_{vpclmul,pclmul,pmull}`):** Accumulates unreduced 255-bit carryless products across arbitrary slice lengths (`4 × vpclmulqdq` per 2-lane `YMM` pair on Alder Lake; `pclmulqdq` on Milan; `pmull` / `pmull2` on ARM64) and performs a single deferred 2-step reduction modulo $z^{128} + z^7 + z^2 + z + 1$ (`0x87`) at the end of the dot product.
- **Basis change ($\mathcal{T}_7 \leftrightarrow \mathbb{F}_2[z]/(z^{128}+z^7+z^2+z+1)$) with public-offset tables.** `tower128_bdoz_2lane_mac_with_backend` (`src/lib.rs`) returns the portable MAC for `SimdBackend::Portable`; otherwise it converts the operands to the polynomial basis in chunks of 32 pairs, calls `tower128_bdoz_2lane_poly_mac_with_backend`, and converts the two accumulators back with `poly128_to_tower128_ct`. The conversion is a fixed $128 \times 128$ matrix over $\mathbb{F}_2$, and each implementation reads constant tables whose **addresses depend only on public loop indices**; the secret is always the data operand, never an index into memory:
  - **Single element, `linear_map::map`.** The matrix is stored as `ByteMatrices([[u64; 16]; 16])`: for each of 16 input bytes and 16 output bytes, one $8 \times 8$ bit matrix in `VGF2P8AFFINEQB` row order (`#[repr(C, align(64))]`, $16 \cdot 16 \cdot 8 = 2{,}048$ bytes per table). `FORWARD` and `INVERSE` serve GFNI; `CONV_FORWARD` and `CONV_INVERSE` are the bit-reversed forms for the carryless-multiply path. With GFNI, `gfni128` (SSE) or `gfni512` (AVX-512) broadcasts each secret input byte and applies `gf2p8affineqb` with the matrix row block as the operand, accumulating by XOR; the matrix operand is loaded with `_mm_load_si128` / `_mm512_load_si512` at offsets fixed by the public byte position. Without GFNI but with `PCLMULQDQ` and `BMI2`, `pclmul_map` runs; on `aarch64` with `PMULL`, `pmull_map` computes the eight parities of each matrix by `vmull_p64` and a shift-and-mask. Otherwise `tower128_to_poly128_portable` / `poly128_to_tower128_portable` XOR the 128 `u128` columns of `T7_TO_POLY_BASIS` / `POLY_TO_T7_BASIS` under masks derived from the input bits, with literal shift counts.
  - **Batch of 64, `tower128_to_poly128_x64_ct`**, used once a chunk has at least `BITSLICED_BASIS_CHANGE_MIN_PAIRS = 4` pairs. With GFNI it calls `linear_map::map_batch` (`gfni512x8` shares each matrix load across eight inputs under AVX-512). Otherwise it bitslices the 64 elements into 128 coefficient planes with `transpose64x64` and applies the method of four Russians: for each of 32 four-column groups it builds on the stack a 16-entry table of XOR combinations of four secret planes, then for each of the 128 output planes XORs in the entry chosen by `T7_TO_POLY_SELECTORS[g][i]`. `T7_TO_POLY_SELECTORS : [[u8; 128]; 32]` is a 4,096-byte static of **public** nibbles computed at compile time from the basis. The 16-entry table holds secret data, but the index into it is public, so the sequence of addresses read is the same for every input. Planes, output and table are wiped with `volatile_fill`.
  - Neither path uses `vpshufb` or `tbl` for the $\mathcal{T}_7$ map; those register lookups belong to the $\mathcal{T}_3$ Shamir kernels of Section 3.2. Their address-independence argument is that a secret may select *within a register* (`vpshufb`, `tbl`) or be the *data* operand of an affine or carryless multiply, and it never forms a memory address. Constant-time behavior also requires secret-independent control flow and the instruction-timing assumptions; address independence alone is insufficient.
  - The auditor rejects static lookup symbols of 4 KiB or more named `TOWER128_ISO`; that rule concerns the removed 16 KiB secret-indexed isomorphism table and does not assert the absence of the constant matrices above.
  - Converted stack buffers (`flat_l`, `flat_r`, `conv_l`, `conv_r`, `chunk_poly`) and the accumulators are wiped with `volatile_fill` / `core::ptr::write_volatile`.

### 3.4 Canonical Zero-Branch Goldilocks ($\mathbb{F}_p,\; p = 2^{64} - 2^{32} + 1$) Kernels

- **`qsag_asm_goldilocks_mul_ct_x86_64` & `qsag_asm_goldilocks_mul_ct_aarch64`:** Computes the 128-bit product `prod = lo + 2^64 * (hi_lo + 2^32 * hi_hi)` via `mulx` (`x86_64`) or `mul + umulh` (`aarch64`) and reduces `lo - hi_hi + (2^32 - 1) * hi_lo` into the **strictly canonical interval $[0, p - 1]$ across all $2^{128}$ input pairs `(a, b) ∈ [0, 2^64 - 1]^2`** (including the maximal overflow corner `a = b = 2^64 - 1 = 0xFFFFFFFFFFFFFFFF`, where `(2^64 - 1)^2 mod p = 0xFFFFFFFC00000004`; separately, `2^128 mod p = 0xFFFFFFFE00000001`) using three branchless carry/borrow mask steps (`sbb` on `x86_64`; inverted `PSTATE.C = !borrow` `subs/sbc` + `adds/adc` on `aarch64`).
- **`qsag_asm_goldilocks_dot2_adx_x86_64`:** Dual-carry-chain `mulx + adcx + adox` 2-term 128-bit inner-product accumulator reduced canonically modulo $p$.
- **`qsag_asm_goldilocks_pow7_ct_x86_64`:** Branchless 4-multiply $x \mapsto x^7 \bmod p$ algebraic S-box for Poseidon2/Monolith sponge layers.

---

## 4. Automated Binary Disassembly Audit (`scripts/audit_elf_ct.py`)

`scripts/audit_elf_ct.py` (`crates/qsag-asm/scripts/audit_elf_ct.py` forwards to it) disassembles the compiled `release` `.rlib` (`objdump -d -C -M intel` + `.rodata` symbol table inspection) and cross-assembles both `src/asm/aarch64_kernels.s` (`aarch64-unknown-linux-gnu`) and the inline `global_asm!` block extracted from `src/aarch64_asm.rs` (`arm64-apple-macosx11.0.0`) via `llvm-mc -triple=aarch64-unknown-linux-gnu` or `clang --target=<triple> -c -x assembler` (with **zero** external `-mattr` flags, verifying `.arch armv8.4-a+sha3+crypto` self-sufficiency).

For the hand-written assembly symbols it checks the rules below. Compiled Rust has separate, name-dependent instruction and taint rules; this list is not a whole-program guarantee for every Rust symbol:
- **0 conditional branches** (only public trip-count loop back-edges permitted in loop kernels; 0 branches of any kind in straight-line kernels),
- **0 variable-latency integer divisions** (`div`, `idiv`, `udiv`, `sdiv`),
- **0 secret-indexed or pre-added single-register LUT dereferences** (`[base + idx*scale]`, `vpgather*`, or `add r_ptr, r_tainted; mov ..., [r_ptr]`),
- **0 variable secret-count shifts** (`shl/shr/sar/ror reg, cl`, `shlx/shrx/sarx`, `lslv/lsrv/asrv`),
- **Mandatory `vzeroupper` before `ret`** in every `x86_64` symbol touching `ymm0..ymm31`,
- **Live-at-`ret` NEON hygiene** in the `aarch64` kernels: written caller-saved vector scratch must be zeroed before `ret` (ABI-preserved registers may instead be restored), and a reload after the wipe re-dirties it; compiled SIMD kernels are held to the full caller-saved set `v0..v7`, `v16..v31`,
- **Zero `TOWER128_ISO` `.rodata` lookup symbols of 4 KiB or more** in native `.o` or `.rlib`,
- **Presence of every required symbol**: the 16 + 7 kernels of `EXPECTED_X86_SYMBOLS` / `EXPECTED_AARCH64_SYMBOLS`, the 3 + 2 kernels of `BITSLICE`, and the compiled SIMD entry points of `REQUIRED_SIMD_SYMBOLS`,
- **Negative `#tooth` self-tests**: `run_negative_self_tests` returns 15 (synthetic `je`, `div`, `[rdi + rax*1]`, pre-added `[r8]` LUTs, static-displacement LUTs, a tainted loop counter, `shl rax, cl`, `shlx`, missing `vzeroupper`, `vzeroupper` without zeroing `xmm0`, `cbnz`, `udiv`, `lslv`, unzeroed and re-loaded `v16`, and two Apple/Linux parity mutations), and `self_tests` adds further assertions for the compiled-Rust rules, including the `v24..v31` NEON cases.

| Target / Binary Class | Audited Symbols | Total Instructions | Conditional Secret Branches | `div`/`udiv` | Secret LUT / Gather | Variable `cl`/`lslv` Shifts | `vzeroupper` / `v16..v20` Wipe | Result |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: |
| `x86_64` Global ASM (`x86_64_asm.rs`) | 16 | 1019 | 0 | 0 | 0 | 0 | Verified | **PASS** |
| `bitslice.rs` ASM (3 `x86_64` + 2 `aarch64`) | 5 | not recorded here | — | — | — | — | — | audited in the compiled ELF |
| Compiled Rust Crypto Fns (native `.o` or `.rlib`) | 22 | 8,043 | — | 0 | 0 | 0 | Verified | **PASS** |
| Linux ELF `aarch64` (`aarch64_kernels.s`) | 7 | 299 | 0 | 0 | 0 | 0 | Verified | **PASS** |
| Apple Mach-O `aarch64` (`aarch64_asm.rs`) | 7 | 299 | 0 | 0 | 0 | 0 | Verified | **PASS** |
| Negative `#tooth` Self-Tests | 15 | — | Caught | Caught | Caught | Caught | Caught | **PASS** |

The instruction counts in this table were recorded for the 16 + 7 kernel set and have not been
regenerated for this revision of the document (the audit needs a Linux release build). The
five `bitslice.rs` kernels are part of the audited set but no instruction count for them is
recorded here; the Lean fixtures (`lean/Qsag/Machine/ElfFixtures.lean`, `lean/Qsag/Machine/ElfFixtureVerify.lean`) cover all 19 + 9 symbols.

---

## 5. Empirical `dudect` Welch's $t$-Tests & Throughput Benchmarks

Following Reparaz–Balasch–Verbauwhede (*dudect*, DATE 2017), `examples/ct_dudect.rs` (and the fast `tests/ct_dudect.rs` integration gate controlled via `QSAG_DUDECT_SAMPLES`) measures cycle-accurate execution latencies (`lfence + rdtsc` on `x86_64`; `isb + mrs cntvct_el0` on `aarch64`) across **randomly interleaved Fixed-All-Zero (`Class 0`) vs Pseudorandom (`Class 1`)** secret inputs, reporting **both** uncropped `t(raw)` and Welford online percentile-cropped Welch-$t$ statistics (`p50..p99`), gated at $|t| < 4.5$ alongside a `#tooth` early-exit tag comparison negative control.

### 5.1 Intel Core i9-12900 (Alder Lake), `X86Avx2GfniVpclmul`

- **Capabilities:** `avx2=true bmi2=true adx=true pclmul=true gfni=true vpclmul=true arch_cap_msr=true doitm=false`
- **Traces per Kernel:** `1,000,192` (+ `10,240` warmup)
- **Negative `#tooth` Control (`early_exit_tag`):** `max|t| = 21,874.51` (`c0 = 37.5 cyc`, `c1 = 5,454.4 cyc`) $\to$ **LEAK DETECTED**

| Kernel Symbol | Traces | `t(raw)` | `t(p50)` | `t(p90)` | `t(p99)` | Cropped `max\|t\|` | Gate (`< 4.5`) |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: | :---: |
| `qsag_asm_keccak_f1600_x4` | 1,000,192 | `+0.36` | `-0.05` | `-0.66` | `-1.12` | `1.12` | **PASS** |
| `qsag_asm_keccak_chi_mpc_row256` | 1,000,192 | `+0.39` | `+0.03` | `-0.10` | `+0.64` | `0.81` | **PASS** |
| `qsag_asm_gf256_shamir_mul` (`GFNI`) | 1,000,192 | `-1.67` | `-1.16` | `-0.18` | `+0.34` | `1.16` | **PASS** |
| `qsag_asm_gf256_shamir_mac` (`GFNI`) | 1,000,192 | `+0.92` | `+0.95` | `+0.90` | `+0.06` | `0.95` | **PASS** |
| `qsag_asm_tower128_bdoz_poly_mac` (`VPCLMUL`) | 1,000,192 | `+0.90` | `-0.84` | `-0.24` | `-0.31` | `0.84` | **PASS** |
| `qsag_asm_tower128_bdoz_t7_mac` ($\mathcal{T}_7$ basis, no secret-indexed LUT) | 1,000,192 | `-1.61` | `-0.14` | `-0.70` | `-1.68` | `1.68` | **PASS** |
| `qsag_asm_goldilocks_pow7_ct` | 1,000,192 | `+0.83` | `-1.09` | `-0.95` | `-1.33` | `1.33` | **PASS** |
| `qsag_asm_goldilocks_dot2_adx` | 1,000,192 | `-1.01` | `-1.00` | `-0.37` | `-0.60` | `1.02` | **PASS** |
| `qsag_asm_ct_eq_32` | 1,000,192 | `+0.39` | `-0.23` | `+0.74` | `+0.19` | `1.00` | **PASS** |

### 5.2 AMD EPYC-Milan (Zen 3), `X86Avx2Pclmul`

- **Capabilities:** `avx2=true bmi2=true adx=true pclmul=true gfni=false vpclmul=false arch_cap_msr=false doitm=false`
- **Traces per Kernel:** `1,000,192` (+ `10,240` warmup)
- **Negative `#tooth` Control (`early_exit_tag`):** `max|t| = 1,607.56` (`c0 = 68.8 cyc`, `c1 = 3,866.0 cyc`) $\to$ **LEAK DETECTED**

| Kernel Symbol | Traces | `t(raw)` | `t(p50)` | `t(p90)` | `t(p99)` | Cropped `max\|t\|` | Gate (`< 4.5`) |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: | :---: |
| `qsag_asm_keccak_f1600_x4` | 1,000,192 | `+0.03` | `+0.63` | `+1.44` | `+1.31` | `1.44` | **PASS** |
| `qsag_asm_keccak_chi_mpc_row256` | 1,000,192 | `+0.62` | `+1.03` | `+1.03` | `+1.03` | `1.03` | **PASS** |
| `qsag_asm_gf256_shamir_mul` (`AVX2` `vpshufb`) | 1,000,192 | `-1.82` | `-1.19` | `+0.64` | `+0.64` | `1.19` | **PASS** |
| `qsag_asm_gf256_shamir_mac` (`AVX2` `vpshufb`) | 1,000,192 | `-0.63` | `+0.00` | `-0.16` | `-0.16` | `0.16` | **PASS** |
| `qsag_asm_tower128_bdoz_poly_mac` (`PCLMUL`) | 1,000,192 | `+0.03` | `+0.39` | `+0.39` | `+0.56` | `0.56` | **PASS** |
| `qsag_asm_tower128_bdoz_t7_mac` ($\mathcal{T}_7$ basis, no secret-indexed LUT) | 1,000,192 | `+1.87` | `-0.46` | `-0.32` | `-0.72` | `0.72` | **PASS** |
| `qsag_asm_goldilocks_pow7_ct` | 1,000,192 | `-0.92` | `+0.03` | `+0.03` | `-0.45` | `0.45` | **PASS** |
| `qsag_asm_goldilocks_dot2_adx` | 1,000,192 | `-0.61` | `-0.58` | `-0.58` | `+1.00` | `1.00` | **PASS** |
| `qsag_asm_ct_eq_32` | 1,000,192 | `-0.58` | `+0.16` | `+0.16` | `+0.16` | `0.16` | **PASS** |

### 5.3 Median Cycle Throughput Speedups (Portable Constant-Time vs Platform SIMD/ASM)

| Operation (Unit) | `Intel Core i9-12900 (Alder Lake)` Portable | `Intel Core i9-12900 (Alder Lake)` SIMD/ASM | `Intel Core i9-12900 (Alder Lake)` Speedup | `AMD EPYC-Milan (Zen 3)` Portable | `AMD EPYC-Milan (Zen 3)` SIMD/ASM | `AMD EPYC-Milan (Zen 3)` Speedup |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: |
| `Keccak-f[1600]` (cycles / sponge) | `652.66` | `272.52` | **2.39×** | `1193.16` | `279.99` | **4.26×** |
| `GF(2^8)` $\mathcal{T}_3$ Shamir Mul (cycles / B) | `19.890` | `0.039` | **505.2×** | `28.274` | `0.551` | **51.3×** |
| `GF(2^8)` $\mathcal{T}_3$ Shamir MAC (cycles / B) | `19.498` | `0.038` | **517.0×** | `27.637` | `0.076` | **365.0×** |
| `Tower128` 2-Lane Poly BDOZ MAC (cycles / pair) | `603.00` | `50.11` | **12.0×** | `774.31` | `76.59` | **10.1×** |
| `Tower128` Wiedemann $\mathcal{T}_7$ BDOZ MAC (cycles / pair) | `3392.88` | `707.07` | **4.8×** | `4792.90` | `1122.72` | **4.3×** |
| `Goldilocks` Canonical Mul (cycles / mul) | `11.56` | `7.66` | **1.51×** | `10.63` | `9.75` | **1.09×** |

---

## 6. Lean 4.35 Formal Machine-Code Verification (`lean/Qsag/Machine/`)

There are two instruction models, and they should not be confused.

**The hand-written AST model, `lean/Qsag/Machine/ConstantTimeIsa.lean`** (3,025 lines, `8` `@[expose]`). It defines `LeakageEvent` traces (`pc`, `branchTaken`, `memAddrs`, `varLatencyOperands`, `dirtyUpperYmmOnRet`) and a static taint checker for `X86Instr` / `ArmInstr` programs that are maintained by hand. Its header says so directly: no `qsag-asm` kernel is modelled there. `lean/Qsag/Machine/FaultAndSpeculativeSafety.lean` builds its speculative-execution model on it.

**The byte-decoded model, `lean/Qsag/Machine/IsaCt.lean`** with the `X86*`, `Arm64*` and `Isa*` modules. Programs are obtained by decoding symbol bytes extracted from the compiled `qsag-asm` archives (`ElfFixtures.lean`, parsed by `ArParse.lean`, `Elf64Parse.lean`, `ElfParse.lean`). Every statement about a `qsag-asm` kernel is made in this model.

| Module | Key theorems | What is kernel-proved |
| :--- | :--- | :--- |
| `ConstantTimeIsa.lean` | `x86_ct_checker_sound`, `arm_ct_checker_sound`, `checkX86Instr_sound`, `checkArmInstr_sound`, `checkX86Block_sound`, `checkArmBlock_sound`, `checkX86Loop_sound`, `checkArmLoop_sound`, `checkX86RetStackPop_sound` | For the hand-written AST: a program accepted by the taint checker has identical `LeakageEvent` traces on any two states that agree on public inputs. |
| `ConstantTimeIsa.lean` (16 `tooth_*` theorems) | `tooth_secret_jcc_leaks_and_rejected`, `tooth_secret_shr_cf_sbb_rejected`, `tooth_secret_mem_index_leaks_and_rejected`, `tooth_secret_div64_leaks_even_under_doit`, `tooth_dirty_ymm_ret_rejected_and_flagged`, `tooth_arm_csel_requires_msr_dit1`, `tooth_arm_umulh_requires_dit`, `tooth_secret_pmull_requires_dit`, `tooth_rorImm64_cannot_launder_secret_zf`, `tooth_shrImm64_cnt2_undef_of_tainted_sec`, `tooth_div64_faults_on_zero_and_quotient_overflow`, `tooth_byteMem64_unaligned_overlap_offsets_1_to_7`, `tooth_byteMem256_partial_overlap_offset_4`, `tooth_secret_rsp_ret_stack_pop_rejected`, `tooth_x86_multiply_without_doit_rejected`, `tooth_x86_mulx_without_doit_leaks` | Checker refusal and, where stated, concrete two-state trace divergence: secret branches, secret memory indices, `div` even under DOIT, a dirty upper `ymm` at `ret`, `csel` / `umulh` / `pmull` without DIT, x86 multiplies without DOIT, flag laundering through shifts, and the byte-memory overlap cases. |
| `IsaCt.lean` | `checkX86ThreeWayNI_sound`, `checkArm64ThreeWayNI_sound`, `checkX86WithInv_sound`, `checkArm64WithInv_sound`, `checkX86_refines_leakage_contract`, `checkArm64_refines_leakage_contract` | Soundness of the decoded-instruction checker, with and without a supplied invariant. |
| `ElfVerify.lean` | `currentX86SymbolContracts` (19), `currentAarch64SymbolContracts` (9), `checkElfSliceThreeWayNI_sound`, `checkElfFuncThreeWayNI_sound`, `checkElfSliceWithCert_sound`, `certSliceAt_sound` | Per-symbol contracts (which argument registers are public pointers or counts) and the theorem that an accepted ELF slice certificate implies trace noninterference. |
| `ElfFixtureVerify.lean`, `ElfInvCerts.lean` | `currentX86_all_symbols_decode`, `currentAarch64_all_symbols_decode`, `currentX86_all_symbol_certificates`, `currentAarch64_all_symbol_certificates`, `currentX86_rlib_every_symbol_three_way_ni_sound`, `currentAarch64_rlib_every_symbol_three_way_ni_sound` | All 28 extracted symbols decode (1,935 `x86_64` and 1,420 `aarch64` instructions), each carries a kernel-checked inductive invariant certificate, and each satisfies three-way noninterference under its contract. Teeth on the real bytes: `current_gfni_missing_vector_cleanup_rejected`, `current_pmull_missing_wipe_rejected`, `mutant_unwiped_neon_reg_rejected`, `mutant_missing_vector_cleanup_rejected`, `current_certificate_mutation_tooth`. |
| `McRefine.lean` | `current_ct_eq_32_x86_64_mc_refines`, `current_ct_eq_32_aarch64_mc_refines`, `current_ct_memzero_x86_64_mc_refines`, `current_ct_memzero_aarch64_mc_refines`, `current_ct_eq_bytes_x86_64_mc_refines`, `current_goldilocks_add_ct_x86_64_mc_refines`, `current_goldilocks_sub_ct_x86_64_mc_refines`, `current_goldilocks_mul_ct_x86_64_mc_refines`, `current_goldilocks_mul_ct_aarch64_mc_refines` | Input/output refinement of nine decoded symbols: the final state of the bounded-fuel run is related to a specification over the initial registers and memory. Each has `*_mutant_refuted` and, where a branch is possible, `*_secret_branch_rejected` teeth. |
| `ElfFunctionalEquiv.lean` | `current_rlib_gf256_shamir_mul_gfni_functional_and_ct`, `current_rlib_gf256_shamir_mul_gfni_loop_functional`, `current_gf256_shamir_mac_gfni_loop_functional`, `current_gf256_shamir_mul_avx2_loop_functional`, `current_gf256_shamir_mac_avx2_loop_functional`, `current_rlib_goldilocks_pow7_ct_x86_64_functional_and_ct`, `current_rlib_goldilocks_dot2_adx_x86_64_functional_and_ct`, `current_rlib_keccak_sha3_neon_functional_and_ct`, `keccakChiMpc_current_functional`, `keccakChiMpc_current_reconstruct`, `keccakThetaRho_current_functional` | Functional equivalence of selected compiled byte slices. Also includes `current_rlib_keccak_f1600_avx2_4x_functional` for the full permutation under `keccak4xFullEntry`; its header count of 12 predates that result. Full functional coverage of all 28 is not established by this list. |
| `SydTv.lean` | `ct_memzero_x86_64_sydtv_refines_all_n`, `ct_memzero_aarch64_sydtv_refines_all_n`, `ct_eq_bytes_x86_64_sydtv_refines_all_n`, `gf256_shamir_mac_gfni_sydtv_refines_all_n`, `tower128_bdoz_mac_vpclmul_sydtv_refines_all_n` (each with a `*_sydtv_refines_pos`) | Cut-point translation validation of five looping kernels for an arbitrary trip count. For `n ≠ 0` the `*_pos` theorems are about the symbol bytes. The `*_all_n` theorems are about `*GuardedRun` runners that add the wrapper's early return for `n = 0` as a hand-written branch: a model of the Rust wrapper, not decoded machine code. `tooth_unguarded_zero_count_wraps_counter` shows what the raw memzero symbol does on a zero count. |
| `ClmulSimd.lean`, `Gf128ClmulLoopAgreement.lean` | `transpose64x256_avx2_code_is_fixture_slice`, `gf2_128_mul_acc_pclmul_code_is_fixture_slice`, `gf2_128_mul_acc_vpclmul_code_is_fixture_slice`, `gf2_128_mul_acc_pmull_code_is_fixture_slice`, `clmul128_eq_four_pclmulqdq`, `gf2_128_reduce_exact`, `gf2_128_mul_bv_eq_rustGf128Mul` | A byte-level SIMD interpreter for the transpose and the three `gf2_128_mul_acc_*` bitslice kernels with instruction-coverage certificates, the carry-less product and reduction proofs, and agreement with the Rust shift-and-reduce loop. |
| `PlatformContractInstances.lean` | `rlib_x86_all19_dit_trace_data_independent`, `rlib_aarch64_all9_dit_trace_data_independent`, `tooth_rlib_x86_gfni_missing_vzeroupper_rejected`, `tooth_rlib_aarch64_pmull_missing_neon_wipe_rejected` | The 28 symbol contracts as instances of `Spec.DitHardwareContract` (see [PROOF_ARCHITECTURE.md](PROOF_ARCHITECTURE.md), Section 5.5). |

What these theorems do not cover: the compiled-Rust SIMD modules (`avx512.rs`, `gf256_simd.rs`, `linear_map.rs`, `ntt_simd.rs`, `sha2_hw.rs`, `aarch64_simd.rs`), the Rust dispatchers and wrappers, and therefore the path that actually runs on a non-GFNI `x86_64` host for Shamir arithmetic or on any host for the $\mathcal{T}_7$ basis change. Those rest on the instruction-rule audit of Section 4 and the timing harness of Section 5. The fixtures are byte snapshots of two archives; that a given release was built from the same bytes is checked by the auditor's fixture mode, not by Lean.

The binary-audit build uses `CARGO_PROFILE_RELEASE_LTO=false cargo rustc -p qsag-asm
--release --lib -- -C lto=no --emit=obj` to obtain native machine code rather than a
thin-LTO bitcode object. Tool discovery prefers `llvm-mc-19`/`llvm-mc` and
`llvm-objdump-19`/`llvm-objdump`, with clang cross-assembly and the LLVM 19 C disassembler
as fallbacks. Apple/Linux AArch64 parity requires identical instruction counts and
normalized mnemonic sequences for every Apple kernel. Fifteen auditor mutation tests
include dropped-instruction and substituted-mnemonic parity failures;
`ConstantTimeIsa.lean` has sixteen `tooth_*` theorems, all listed in the table above.

The Wiedemann generator checks deliberately use the implemented relations
`X0² + X0 = 1` and `Xk² + X(k−1)Xk = 1`. For this basis, `Phi(0x04)² + Phi(0x04) = 0x5D`
and `Phi(0x10)² + Phi(0x10) = 0xA1`; the alternative Artin–Schreier relations with unit
linear coefficient are not identities of these byte generators.

Post-hardening validation (2026-11-13): both Intel Core i9-12900 (Alder Lake) and
AMD EPYC-Milan (Zen 3) passed the 10-operation harness with
`QSAG_DUDECT_SAMPLES=100000` (rounded to 100,096 samples per operation). The largest
reported statistic was 2.62 on Intel and 2.23 on AMD, below the 4.5 gate; both negative
controls detected leakage. The million-trace and throughput tables above are historical
measurements, not the sample counts of this hardening run. Binary counts in section 4
include disassembler-reported alignment padding and depend on compiler configuration.

`ConstantTimeIsa.lean` retains eight `@[expose]` declarations and imports only
`Qsag.Tactic.AssuranceKit` and `Qsag.Tactic.Prelude`. Axiom dependencies of every `Machine/`
declaration are checked by the library-wide `AuditAxioms` gate
([PROOF_ARCHITECTURE.md](PROOF_ARCHITECTURE.md), Section 7); no build timing is recorded here
for the current tree.
