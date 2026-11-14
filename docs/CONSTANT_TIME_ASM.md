# `qsag-asm` & `Qsag.ConstantTimeIsa`: Platform SIMD Assembly, Formal Machine-Code Noninterference, and Empirical Timing Verification

This document specifies **Pillar 3** of qsag — Quorum-Switching AGgregation / Quantum Succinct AGgregation:

1. **`crates/qsag-asm`**: Zero-dependency `#![no_std]` hand-crafted platform assembly kernels for `x86_64` (`AVX2`, `GFNI`, `VPCLMULQDQ`/`PCLMULQDQ`, `BMI2`/`ADX`) and `aarch64` (`ARMv8.2-SHA3`, `PMULL`, `NEON`, `ARMv8.4-DIT`), backed by runtime `CPUID`/`XGETBV`/`AT_HWCAP`/`sysctlbyname` capability probing and a 100% branchless, table-free portable fallback.
2. **`crates/qsag-asm/scripts/audit_elf_ct.py`**: Automated static binary disassembly verifier auditing every `x86_64` assembly symbol, compiled Rust crypto functions in native `.o` or `.rlib`, and both Linux ELF and Apple Mach-O `aarch64` assembly kernels (paired with 15 negative `#tooth` self-tests).
3. **`lean/Qsag/ConstantTimeIsa.lean`**: Self-contained Lean 4.35 formal machine-code semantics and relational taint-noninterference checker (`0 sorry`, `0 axiom`, `0 native_decide`, `8` `@[expose]`) proving modeled architectural leakage invariance and algebraic functional correctness for the specific modeled programs listed below. Public loops abstract dispatch-guarded positive counts; the ARM equality model expands paired loads into scalar loads.
4. **`crates/qsag-asm/{examples,tests}/ct_dudect.rs`**: Empirical Welch's $t$-test constant-time harness (`1,000,192` cycle-counter traces per kernel in deep mode; `25,600`-trace sub-second CI gate via `QSAG_DUDECT_SAMPLES`), validated on both **Intel Core i9-12900 (`Alder Lake`, `AVX2+GFNI+VPCLMULQDQ`)** and **AMD EPYC-Milan (`Zen 3`, `AVX2+PCLMULQDQ`)**.

Lean timing theorems cover exactly eight modeled programs: AVX2 MPC chi, SHA3 NEON chi,
GFNI Shamir multiplication, VPCLMUL BDOZ MAC, and Goldilocks multiplication and 32-byte
equality on each ISA. Functional program theorems cover Goldilocks, equality, one-block
GFNI output, and AVX2 MPC chi output lane zero. The remaining functional theorems establish
algebraic identities and degree bounds; they do not prove full Keccak-f1600 or the entire
BDOZ MAC implementation. The modeled-program proofs and compiled ELF64 decoding are separate evidence surfaces;
see [binary verification](BINARY_RLIB_VERIFICATION.md) for fixture binding.

The binary auditor covers all 16 x86 kernels (ELF, Windows COFF, Apple Mach-O), all 7
AArch64 kernels (ELF and Mach-O), and emitted Rust crypto functions. Compiled Rust checks
are instruction-rule checks, with stricter branch checks on named straight-line primitives;
they are not whole-program taint proofs. The empirical harness exercises **10 dispatched
operations**, including `qsag_asm_goldilocks_mul_ct`; backend selection determines which
assembly implementation runs. A passing timing sample is evidence, not universal timing proof.

---

## Grounded ISA integration and scope

`ConstantTimeIsa.lean` and `ElfBinaryVerify.lean` are the ISA/ELF pillar alongside
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
   - Zero secret-indexed table lookups (`[base + secret * scale]`, `vpgather*`, `pshufb`/`tbl` secret-table scans) exist in either assembly or portable fallback paths.
   - All `Tower` $\mathcal{T}_3 \cong \mathbb{F}_{2^8}$ and $\mathcal{T}_7 \cong \mathbb{F}_{2^{128}}$ basis conversions execute strictly in registers (`vgf2p8affineqb` on GFNI, nibble `vpshufb` over 16-byte register broadcasts on AVX2, and a register-resident 128-word bit-matrix on $\mathcal{T}_7$ with **zero** static cache-resident lookup tables).
3. **Fixed-Latency Operand Discipline & Hardware `DIT` / `DOITM`:**
   - The instruction rules reject variable-latency integer dividers (`div`, `idiv`, `udiv`, `sdiv`) and secret-count variable shifts in audited paths. This does not establish coverage of every compiled Rust routine.
   - Conditional data selection uses pure fixed-latency ALU carry/borrow masks (`sbb reg, reg` on `x86_64`; `sbc reg, xzr, xzr` / `adc reg, xzr, xzr` + `neg` on `aarch64` — avoiding `cmovcc`, `csel`, `cset`, and `csetm` when hardware DIT is inactive).
   - `enable_hardware_dit()` (`crates/qsag-asm/src/cpuid.rs`) executes `msr dit, #1` (`PSTATE.DIT = 1`) in EL0 userspace **only** after verifying runtime `AT_HWCAP` (`HWCAP_DIT = 1 << 24` on Linux) or `sysctlbyname("hw.optional.arm.FEAT_DIT")` on Apple Silicon (preventing `SIGILL` on pre-ARMv8.4 cores). On `x86_64`, `CPUID.(EAX=7,ECX=2):EDX[29]` enumerates `IA32_ARCH_CAPABILITIES` MSR presence (`x86_arch_capabilities_msr`), while `x86_doit_enumerated` remains `false` in unprivileged ring-3 because `IA32_ARCH_CAPABILITIES[12]` (`DOITM`) and `IA32_UARCH_MISC_CTL[0]` require ring-0 `RDMSR`/`WRMSR`.
4. **Architectural & Scratch Zeroization:**
   - Every `AVX2` kernel wipes scratch `ymm` registers via `vpxor ymm, ymm, ymm` and executes `vzeroupper` prior to `ret` (preventing dirty upper-YMM AVX$\leftrightarrow$SSE transition penalties and residual secret state in touched SIMD scratch registers).
   - Every `aarch64` NEON/SHA3/PMULL kernel (both Linux ELF `src/asm/aarch64_kernels.s` and Apple Mach-O `src/aarch64_asm.rs`) preserves AAPCS64 callee-saved `d8..d15` (saving/restoring full 128-bit `q8..q15` where needed) and explicitly wipes touched caller-saved vector registers via `eor vN.16b, vN.16b, vN.16b` before `ret`.
   - Temporary stack buffers holding secret shares or basis-converted field elements (`b0`, `b1`, `chunk_poly`, `poly_acc*`) are wiped via `ct_memzero` / `core::ptr::write_volatile` before scope exit.

---

## 2. Cross-Platform ABI & Runtime Dispatch Architecture

### 2.1 Explicit `extern "sysv64"` Calling Convention (`x86_64`)

All 16 `x86_64` `global_asm!` kernels follow the System V AMD64 register convention (`rdi, rsi, rdx, rcx, r8, r9`; `rbx, rbp, r12..r15` callee-saved). Every Rust FFI declaration and call wrapper in `crates/qsag-asm/src/x86_64_asm.rs` is typed `unsafe extern "sysv64" fn(...)` rather than `extern "C"`, guaranteeing that on `x86_64-pc-windows-msvc` / `x86_64-pc-windows-gnu` LLVM automatically bridges Windows x64 arguments (`rcx, rdx, r8, r9`) and preserves Windows non-volatile registers (`rdi, rsi, xmm6..xmm15`). Stack pointers remain 16-byte aligned with zero red-zone (`[rsp - disp]`) accesses.

### 2.2 Lock-Free Runtime Backend Selection

`detect_backend()` (`crates/qsag-asm/src/cpuid.rs`) caches one of four backend tiers in an `AtomicU8`:

| `SimdBackend` Tier | Target ISA & Required Extensions | Verified Host |
| :--- | :--- | :--- |
| `X86Avx2GfniVpclmul` | `x86_64` + OS `XGETBV(XCR0[2:1]=11b)` + `AVX2` + `BMI1` + `BMI2` + `ADX` + `GFNI` + `VPCLMULQDQ` | Intel Core i9-12900 (Alder Lake) |
| `X86Avx2Pclmul` | `x86_64` + OS `XGETBV(XCR0[2:1]=11b)` + `AVX2` + `BMI1` + `BMI2` + `ADX` + `PCLMULQDQ` | AMD EPYC-Milan (Zen 3) |
| `Aarch64NeonSha3Pmull` | `aarch64` + `AdvSIMD` + `FEAT_SHA3` (`eor3`/`rax1`/`xar`/`bcax`) + `FEAT_PMULL` | Linux `AT_HWCAP` / Apple `sysctlbyname` |
| `Portable` | Pure `#![no_std]` branchless, LUT-free, `cl`-shift-free Rust | All targets (`cargo test` cross-tier parity) |

Both `src/asm/aarch64_kernels.s` and `src/aarch64_asm.rs` emit `.arch armv8.4-a+sha3+crypto` inside the assembly translation unit so baseline `aarch64-unknown-linux-gnu` builds compile cleanly without global `-C target-feature` flags while guarding execution behind runtime `AT_HWCAP` / `sysctlbyname` checks.

---

## 3. Algebraic Basis Isomorphisms & Kernel Designs

### 3.1 4-Way Parallel `Keccak-f[1600]` & 256-Way Bitsliced 3-Party RSS MPC $\chi$

- **`qsag_asm_keccak_f1600_avx2_4x` (`x86_64` AVX2):** Evaluates 4 independent 1600-bit sponges (`25 × u64 × 4` lanes = `800 B` interleaved in `25 × YMM`) across all 24 rounds in-register, computing $\theta, \rho, \pi, \chi$ (`vpandn + vpxor`), and $\iota$ without spilling state to memory between rounds.
- **`qsag_asm_keccak_chi_mpc_avx2` (`x86_64` AVX2):** Processes **256 parallel Keccak $\chi$-rows simultaneously** (`4 × 64` bits per `YMM`) under 3-party Replicated Secret Sharing (RSS):
  $$z_i^{(x)} = s_i^{(x)} \oplus \bigl(\neg s_i^{(x+1)} \land s_i^{(x+2)}\bigr) \oplus \bigl(t_i^{(x+1)} \land s_i^{(x+2)}\bigr) \oplus m_i^{(x)}$$
  satisfying $\bigoplus_{p \in \{0,1,2\}} z^{(p)} = a \oplus (\neg b \land c)$ for all $a = \bigoplus_p s^{(p)},\; b = \bigoplus_p s^{(p)}_{+1},\; c = \bigoplus_p s^{(p)}_{+2}$ whenever $m^{(0)} \oplus m^{(1)} \oplus m^{(2)} = 0$.
- **`qsag_asm_keccak_sha3_neon` & `qsag_asm_keccak_theta_rho_sha3_neon` (`aarch64` `FEAT_SHA3`):** Executes native 2-way 64-bit SIMD `eor3.16b`, `rax1.2d`, `xar.2d`, and `bcax.16b` (`d = a ^ (b & ~c)`), wired directly into `keccak_f1600_x4_with_backend` under `SimdBackend::Aarch64NeonSha3Pmull`.

### 3.2 Wiedemann Tower $\mathcal{T}_3 \cong \mathbb{F}_{2^8}$ Shamir Kernels (`GFNI` & `AVX2`)

`QSAG` represents $\mathbb{F}_{2^8}$ via the Wiedemann tower $\mathcal{T}_0 = \mathbb{F}_2$, $\mathcal{T}_1 = \mathcal{T}_0[x_0]/(x_0^2 + x_0 + 1)$, $\mathcal{T}_2 = \mathcal{T}_1[x_1]/(x_1^2 + x_0 x_1 + 1)$, $\mathcal{T}_3 = \mathcal{T}_2[x_2]/(x_2^2 + x_1 x_2 + 1)$, whereas Intel `VGF2P8MULB` multiplies in the AES polynomial basis $\mathbb{F}_2[z]/(z^8 + z^4 + z^3 + z + 1)$ (`0x11B`).

Mapping the tower generators $(1, x_0, x_1, x_0 x_1, x_2, x_0 x_2, x_1 x_2, x_0 x_1 x_2)$ to roots in $\mathbb{F}_2[z]/(z^8 + z^4 + z^3 + z + 1)$:
- $\phi(x_0) = \text{0xBC}$ ($\phi(x_0)^2 \oplus \phi(x_0) = 1$),
- $\phi(x_1) = \text{0xB0}$ ($\phi(x_1)^2 \oplus \phi(x_0)\phi(x_1) = 1$),
- $\phi(x_2) = \text{0x63}$ ($\phi(x_2)^2 \oplus \phi(x_1)\phi(x_2) = 1$).

yields the exact `VGF2P8AFFINEQB` $8\times 8$ bit-matrices (packed MSB-first per `VGF2P8AFFINEQB` lane semantics):
- `GFNI_TOWER_TO_POLY_MAT = 0x71500A8A86BE78CE` ($\phi : \mathcal{T}_3 \xrightarrow{\sim} \mathbb{F}_2[z]/(z^8 + z^4 + z^3 + z + 1)$)
- `GFNI_POLY_TO_TOWER_MAT = 0xA1E4F8E072A2700C` ($\phi^{-1} : \mathbb{F}_2[z]/(z^8 + z^4 + z^3 + z + 1) \xrightarrow{\sim} \mathcal{T}_3$)

`qsag_asm_gf256_shamir_mul_gfni` and `qsag_asm_gf256_shamir_mac_gfni` evaluate **32 parallel $\mathcal{T}_3$ multiplications per `YMM` vector** via $\phi^{-1}(\phi(a) \cdot_{\text{0x11B}} \phi(b))$ (with $\phi$ lifted out of the inner loop in `mac_gfni`), achieving **505.2×** (`mul`) and **517.0×** (`mac`) throughput speedups over constant-time portable code on `Intel Core i9-12900 (Alder Lake)`. On CPUs without GFNI (AMD EPYC-Milan (Zen 3)), `qsag_asm_gf256_shamir_mul_avx2` and `qsag_asm_gf256_shamir_mac_avx2` use constant-time register-resident `vpshufb` nibble tables over $\phi(a), \phi(b)$, achieving **51.3×** (`mul`) and **365.0×** (`mac`) speedups with **100% bit-exact parity across all $2^{16} = 65,536$ input byte pairs**.

### 3.3 2-Lane $\mathbb{F}_{2^{128}}$ BDOZ MAC (`VPCLMULQDQ` / `PCLMULQDQ` / `PMULL`) & LUT-Free $\mathcal{T}_7$ Isomorphism

- **Polynomial-Basis Inner Product (`qsag_asm_tower128_bdoz_mac_{vpclmul,pclmul,pmull}`):** Accumulates unreduced 255-bit carryless products across arbitrary slice lengths (`4 × vpclmulqdq` per 2-lane `YMM` pair on Alder Lake; `pclmulqdq` on Milan; `pmull` / `pmull2` on ARM64) and performs a single deferred 2-step reduction modulo $z^{128} + z^7 + z^2 + z + 1$ (`0x87`) at the end of the dot product.
- **Zero-Table Register Isomorphism ($\mathcal{T}_7 \leftrightarrow \mathbb{F}_2[z]/(z^{128}+z^7+z^2+z+1)$):** `tower128_bdoz_2lane_mac_with_backend` converts Wiedemann $\mathcal{T}_7$ elements to and from the polynomial basis via 128 compile-time `u128` basis constants XOR-masked branchlessly in registers using literal bit shifts (`0` cache-resident lookup tables, `0` secret-indexed memory reads, `0` variable `cl` shifts), amortizing the basis change $O(1)$ at the dot-product boundary when `keys` are pre-converted or batching 16-element chunks on stack scratch wiped via `ct_memzero`.

### 3.4 Canonical Zero-Branch Goldilocks ($\mathbb{F}_p,\; p = 2^{64} - 2^{32} + 1$) Kernels

- **`qsag_asm_goldilocks_mul_ct_x86_64` & `qsag_asm_goldilocks_mul_ct_aarch64`:** Computes the 128-bit product `prod = lo + 2^64 * (hi_lo + 2^32 * hi_hi)` via `mulx` (`x86_64`) or `mul + umulh` (`aarch64`) and reduces `lo - hi_hi + (2^32 - 1) * hi_lo` into the **strictly canonical interval $[0, p - 1]$ across all $2^{128}$ input pairs `(a, b) ∈ [0, 2^64 - 1]^2`** (including the maximal overflow corner `a = b = 2^64 - 1 = 0xFFFFFFFFFFFFFFFF`, where `(2^64 - 1)^2 mod p = 0xFFFFFFFC00000004`; separately, `2^128 mod p = 0xFFFFFFFE00000001`) using three branchless carry/borrow mask steps (`sbb` on `x86_64`; inverted `PSTATE.C = !borrow` `subs/sbc` + `adds/adc` on `aarch64`).
- **`qsag_asm_goldilocks_dot2_adx_x86_64`:** Dual-carry-chain `mulx + adcx + adox` 2-term 128-bit inner-product accumulator reduced canonically modulo $p$.
- **`qsag_asm_goldilocks_pow7_ct_x86_64`:** Branchless 4-multiply $x \mapsto x^7 \bmod p$ algebraic S-box for Poseidon2/Monolith sponge layers.

---

## 4. Automated Binary Disassembly Audit (`scripts/audit_elf_ct.py`)

`crates/qsag-asm/scripts/audit_elf_ct.py` disassembles the compiled `release` `.rlib` (`objdump -d -C -M intel` + `.rodata` symbol table inspection) and cross-assembles both `src/asm/aarch64_kernels.s` (`aarch64-unknown-linux-gnu`) and the inline `global_asm!` block extracted from `src/aarch64_asm.rs` (`arm64-apple-macosx11.0.0`) via `llvm-mc -triple=aarch64-unknown-linux-gnu` or `clang --target=<triple> -c -x assembler` (with **zero** external `-mattr` flags, verifying `.arch armv8.4-a+sha3+crypto` self-sufficiency).

For every symbol it enforces:
- **0 conditional branches** (only public trip-count loop back-edges permitted in loop kernels; 0 branches of any kind in straight-line kernels),
- **0 variable-latency integer divisions** (`div`, `idiv`, `udiv`, `sdiv`),
- **0 secret-indexed or pre-added single-register LUT dereferences** (`[base + idx*scale]`, `vpgather*`, or `add r_ptr, r_tainted; mov ..., [r_ptr]`),
- **0 variable secret-count shifts** (`shl/shr/sar/ror reg, cl`, `shlx/shrx/sarx`, `lslv/lsrv/asrv`),
- **Mandatory `vzeroupper` before `ret`** in every `x86_64` symbol touching `ymm0..ymm31`,
- **Mandatory `v16..v20` scratch NEON zeroization before `ret`** in `aarch64` PMULL kernels,
- **Zero oversized `TOWER128_ISO` `.rodata` tables** in native `.o` or `.rlib`,
- **15 built-in `#tooth` negative self-tests** confirming the auditor rejects synthetic `je`, `div`, `[rdi + rax*1]`, pre-added `[r8]` LUTs, `shl rax, cl`, `shlx`, missing `vzeroupper`, `cbnz`, `udiv`, `lslv`, and unzeroed `v16.16b` PMULL gadgets.

| Target / Binary Class | Audited Symbols | Total Instructions | Conditional Secret Branches | `div`/`udiv` | Secret LUT / Gather | Variable `cl`/`lslv` Shifts | `vzeroupper` / `v16..v20` Wipe | Result |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: |
| `x86_64` Global ASM (`x86_64_asm.rs`) | 16 | 1019 | 0 | 0 | 0 | 0 | Verified | **PASS** |
| Compiled Rust Crypto Fns (native `.o` or `.rlib`) | 22 | 8,043 | — | 0 | 0 | 0 | Verified | **PASS** |
| Linux ELF `aarch64` (`aarch64_kernels.s`) | 7 | 299 | 0 | 0 | 0 | 0 | Verified | **PASS** |
| Apple Mach-O `aarch64` (`aarch64_asm.rs`) | 7 | 299 | 0 | 0 | 0 | 0 | Verified | **PASS** |
| Negative `#tooth` Self-Tests | 15 | — | Caught | Caught | Caught | Caught | Caught | **PASS** |

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
| `qsag_asm_tower128_bdoz_t7_mac` (LUT-free $\mathcal{T}_7$) | 1,000,192 | `-1.61` | `-0.14` | `-0.70` | `-1.68` | `1.68` | **PASS** |
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
| `qsag_asm_tower128_bdoz_t7_mac` (LUT-free $\mathcal{T}_7$) | 1,000,192 | `+1.87` | `-0.46` | `-0.32` | `-0.72` | `0.72` | **PASS** |
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

## 6. Lean 4.35 Formal Machine-Code Verification (`lean/Qsag/ConstantTimeIsa.lean`)

`lean/Qsag/ConstantTimeIsa.lean` (`module` + `public section`, `8` `@[expose]`, `0 sorryAx`, `0 Lean.ofReduceBool`) models concrete operational semantics and microarchitectural `LeakageEvent` traces (`pc`, `branchTaken`, `memAddrs`, `varLatencyOperands`, `dirtyUpperYmmOnRet`) for both `x86_64` (`X86Gpr`, `YmmReg`, `X86Flags`, `X86Instr`, `X86Stmt`) and `aarch64` (`ArmGpr`, `NeonReg`, `ArmFlags`, `ArmInstr`, `ArmStmt`).

| Section / Domain | Key Exported Lean 4 Theorems | What Is Kernel-Proved |
| :--- | :--- | :--- |
| **Relational Taint Checker Soundness** | `x86_ct_checker_sound`, `arm_ct_checker_sound`, `checkX86Instr_sound`, `checkArmInstr_sound` | For any low-equivalent initial states `s₁ ≈_τ s₂` (agreeing only on `Public` inputs/pointers while `Secret` registers and heap shares vary arbitrarily), `check*Prog = some τ'` implies **identical `LeakageEvent` traces** and `s₁' ≈_{τ'} s₂'`. |
| **Negative `#tooth` Mutation Guards** | `tooth_secret_jcc_leaks_and_rejected`, `tooth_secret_mem_index_leaks_and_rejected`, `tooth_secret_div64_leaks_even_under_doit`, `tooth_dirty_ymm_ret_rejected_and_flagged`, `tooth_arm_csel_requires_msr_dit1`, `tooth_secret_shr_cf_sbb_rejected`, `tooth_arm_umulh_requires_dit` | Proves both checker refusal (`none`) and concrete two-state trace divergence on secret conditional branches, secret LUT indexing, `div` even when `DOIT = true`, missing `vzeroupper`, and `csel` without `msr dit, #1`. |
| **Keccak chi & 256-Way MPC $\chi$** | `keccakChiMpc_3party_rss_sound`, `keccakChiMpcAvx2_exec_lane0_correct`, `keccakChiMpcAvx2_constant_time`, `bcax_eq_keccakChiLane`, `keccakSha3Neon_constant_time` | 3-party RSS $\chi$-gate reconstruction identity across all 256 bits (`Vec256`), `ARMv8.2-SHA3` `bcax` equivalence, and timing-noninterference + `ymm0..ymm11` wipe + `vzeroupper` hygiene. |
| **Wiedemann $\mathcal{T}_3 \leftrightarrow$ Intel `GFNI`** | `gfni_phi_left_inv`, `gfni_phi_right_inv`, `gfni_isomorphism_homomorphic`, `gf256ShamirMulGfni_32lane_correct`, `gf256ShamirMulGfni_exec_1block_correct`, `gf256ShamirMulGfni_constant_time` | Proves `0x71500A8A86BE78CE` and `0xA1E4F8E072A2700C` are mutual inverses over $\mathbb{F}_2^8$ and homomorphically map `VGF2P8MULB` (`0x11B`) to `towerGf256Mul` across all 65,536 byte pairs and all 32 `YMM` lanes, plus inductive noninterference for arbitrary `blocks : Nat`. |
| **2-Lane `VPCLMULQDQ` BDOZ MAC** | `tower128BdozVpclmul_constant_time`, `clmul64_0x87_hi_degree_bound` | Inductive timing-noninterference for arbitrary `count : Nat` + `ymm0..ymm8` epilogue wipe + `vzeroupper`, and closed-form proof that `(clmul64 c3 0x87).hi >>> 7 = 0#64` so the 2-step reduction never overflows bit 127. |
| **Goldilocks $\mathbb{F}_p$ Cross-ISA Arithmetic** | `goldilocks_reduce128_nat_sound`, `goldilocksMulCtX86_canonical_correct`, `goldilocksMulCt_x86_eq_arm`, `goldilocksMulCtX86_constant_time`, `goldilocksMulCtArm_constant_time`, `goldilocksMulCtX86_scratch_zero`, `goldilocksMulCtArm_scratch_zero` | Universal proof over all $2^{128}$ pairs `(a, b) : BitVec 64 × BitVec 64` (including `(2^64 - 1)^2`) that `qsag_asm_goldilocks_mul_ct_x86_64` and `qsag_asm_goldilocks_mul_ct_aarch64` (with ARM64 inverted `PSTATE.C = !borrow`) return the exact same canonical `< p` residue `(a * b) % p` with zero timing leakage. |
| **Constant-Time 256-Bit Tag Equality** | `or_neg_shr63_xor1_eq_beq_zero`, `ctEq32Arm_functional_correct`, `ctEq32X86_functional_correct`, `ctEq32X86_constant_time`, `ctEq32Arm_constant_time` | Proves `((d \|\|\| -d) >>> 63) ^^^ 1 = (d == 0)` over all `BitVec 64`, end-to-end 4-limb 256-bit tag equality correctness, and secret-tag timing-noninterference. |

The binary-audit build uses `CARGO_PROFILE_RELEASE_LTO=false cargo rustc -p qsag-asm
--release --lib -- -C lto=no --emit=obj` to obtain native machine code rather than a
thin-LTO bitcode object. Tool discovery prefers `llvm-mc-19`/`llvm-mc` and
`llvm-objdump-19`/`llvm-objdump`, with clang cross-assembly and the LLVM 19 C disassembler
as fallbacks. Apple/Linux AArch64 parity requires identical instruction counts and
normalized mnemonic sequences for every Apple kernel. Fifteen auditor mutation tests
include dropped-instruction and substituted-mnemonic parity failures; Lean has seven
`tooth_*` theorems.

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

Final Lean rebuilds completed in 12 seconds on Intel Core i9-12900 (Alder Lake) and
18 seconds on AMD EPYC-Milan (Zen 3), with no errors or warnings. Exported theorem
axiom checks contain no `sorryAx` or `Lean.ofReduceBool`; the module retains eight
`@[expose]` declarations and only the implicit core `Init` import.
