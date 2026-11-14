# Compiled Binary `.rlib` / `ELF64` Machine-Code Verification (`Qsag.ElfBinaryVerify`)

The integrated main-library axiom audit checks **59,257 declarations, including 28,744 kernel theorem declarations, across 57 modules**, with **0 rejected axioms**. This includes private and compiler-generated declarations and 277 pure assurance-infrastructure declarations; 131 compile-time tactic declarations are excluded. Counts describe the checked definitions and premises, not complete production refinement. The combined extracted-MIR and custody audit checks **5,318 declarations / 2,093 theorems / 44 contributing modules**; the WHIR audit checks **1,558 / 718 / 7**. Both report **0 rejected axioms**. Sandboxed six-kernel challenge replay passes 107 main theorems and 65 MIR theorems plus 17 definitions.

## Artifact scope and active integration

Validation on 2026-11-14 (Linux x86-64, Lean 4.35.0, rustc/cargo 1.99.1, z3 5.4.1):

- **Integrated Lean coverage.** `ElfFunctionalEquiv` is now imported by the library root and
  the all-module axiom gate, alongside `ElfBinaryVerify`, `ElfFixtureVerify`, `McRefine`,
  `ConstantTimeIsa`, `SydTvTranslationValidation`, `IsaCosim`, `SimdBinaryEquiv` and
  `SpirvSimtGpuEquiv`. It adds selected byte-pinned functional results, including GFNI tower
  multiplication and AArch64 Keccak, over the historical fixtures. It does not repair freshness.
  The final integrated census is recorded in [the convergence tracker](CONVERGENCE_STATUS.md).
- **SyDTV.** `SydTvTranslationValidation` was migrated to the corrected `stepX86` flag semantics
  (architectural `OF` for `SUB`/`ADD`/`INC`/`DEC`, `CF`/`OF` for `SHR`). For each of the five loop
  kernels it now has a `*_sydtv_refines_pos` theorem stated on `runX86One` / `runArm64One` over
  the symbol bytes for a nonzero count. The `*_sydtv_refines_all_n` theorems are about the
  guarded runners, whose zero-count branch is a hand-written model of the Rust wrappers' early
  return and is not decoded machine code. The VPCLMUL byte list is bound to archive slice 6.
  `python3 scripts/sydtv_driver.py --self-test --require-z3 --check-lean` passes: z3 returns
  `unsat` for both induction cuts and `sat` for the same cuts with the trip-count bound removed,
  and both emitted certificate proposals elaborate against the current certificate API. The
  driver covers the two memzero kernels only; no solver answer is used by a Lean proof.
- **Repeated native comparison.** 7,184 scalar/SIMD vectors, 7,753 executed instructions,
  zero discrepancies and no skipped flag cases. The CPU run was in a Linux VM with native
  instruction execution, not a bare-metal host measurement. SIMD tests covered 512 batches
  per multiply kernel and 512 transpose matrices. AArch64 bytes were extracted, not executed.
- **Instruction screens.** The integrated ELF auditor passed its 34 self-tests, current x86
  archive scan, cross-assembled AArch64 bitslice scan, and linked ThinLTO executable scan.
  This is an instruction screen, not an interprocedural constant-time proof.
- **Fixture freshness: FAIL, measured per kernel.** The archives embedded in
  `CompiledRlibFixtures.lean` do not correspond to the current assembly source, and for x86_64
  they correspond to no committed revision:

  | Source built with the CI command | x86_64 kernels identical to the fixture | AArch64 kernels identical to the fixture | Kernels with no certificate |
  | :--- | ---: | ---: | :--- |
  | working tree (2026-11-14) | 0 of 16 | 6 of 7 (`qsag_asm_goldilocks_mul_ct_aarch64` differs, 116 B → 120 B) | `transpose64x256_avx2`, `gf2_128_mul_acc_pclmul`, `gf2_128_mul_acc_vpclmul`, `transpose64x256_neon`, `gf2_128_mul_acc_pmull` |
  | `git archive b1cd91a` | 0 of 16 | 7 of 7 | the same five |

  Every current x86_64 kernel is 20–25 bytes longer than its certified counterpart (for example
  `qsag_asm_ct_memzero_x86_64`: 19 B certified, 41 B current), so every theorem pinned to x86_64
  fixture bytes describes historical machine code. Object digests (`.rcgu.o`, SHA-256):

  | | x86_64 | AArch64 |
  | :--- | :--- | :--- |
  | certified fixture | `fbe87faf1486cb90698fba4dfd7497b66f50032a70d69abb7cddeaf1ee332702` | `8ca2b4c1c28ee5d653803c2b4aa57681481179243f4addcc15eba797e3be8c7e` |
  | working tree | `c23eb2d7728f7d629d9ffeaacf9f09cb0e596f6b404f9bd7b619ebf4815a78f0` | `fd3064989d545714039f17c103f56bbea3dc74cb511858febcc52cabc98d3a7d` |
  | `b1cd91a` | `fea50f3ea24b7a390886cafbd9baca4bca727b661fe35f8d26df5bf1a02260dc` | `94dd899358232e5b02889d864987ffb28354ac0555bb8b1b08f555efaf7b9dfb` |

  The object digest also depends on the cargo invocation: the same working tree built with an
  explicit `--target x86_64-unknown-linux-gnu` gives `85d7429a…`, because the object contains
  compiled Rust code besides the assembly kernels. `scripts/audit_elf_ct.py --check-fixtures`
  therefore prints a per-kernel verdict and accepts `--fixture-binding kernel-bytes` (identical
  `qsag_asm_*` symbol set and code bytes, which is what the certificates quantify over); the
  default `object` binding is unchanged. Both bindings fail today.

  Refreshing the fixtures is one coordinated change across `CompiledRlibFixtures.lean`,
  `ElfFixtureSlices.lean`, `ElfInvCerts.lean`, the slice-equality proofs in `ElfParse.lean`, the
  contracts in `ElfFixtureVerify.lean` (five new kernels need contracts, and the two transpose
  kernels need decoder coverage), the mutation offsets in `ElfBinaryVerify.lean`, and every
  byte-pinned x86_64 proof in `McRefine.lean`, `SydTvTranslationValidation.lean` and
  `ElfFunctionalEquiv.lean`. It was not started here: a partial refresh would turn the passing
  modules red.
- `Qsag.IsaCosim` contains the pure executor adapter and regression vectors;
  `lean/IsaCosim.lean` imports it for JSON transport.

The SPIR-V module proves codec, scheduling, race-freedom and leakage-model
properties. Runtime shader functional equivalence remains unproved; its former
§4 claim has been removed. Both SPIR-V 1.5 and 1.6 are represented explicitly.


The fixture inventory below records the certificate archives embedded in
`CompiledRlibFixtures.lean`, with decode counts checked by `ElfFixtureVerify.lean`. Its hashes and
instruction counts do not describe every current build. `ElfBinaryVerify.lean`
and `ConstantTimeIsa.lean` connect selected decoded ELF64 bytes to taint
noninterference, scratch zero-on-exit and mutation `#tooth` witnesses. They do not
prove whole-process constant time, whole-process erasure or coverage of all callers.
The source/extraction/byte binding must be renewed after compiler, flags, target,
features, dispatch or assembly changes.

LNSym / x86lean / ELFSage grounding, linked ThinLTO `ET_EXEC`/`ET_DYN` coverage,
complete bitslice symbol coverage and physical x86_64 `lake exe isa-cosim` are
active integration work. x86_64 AVX2/PCLMULQDQ/VPCLMULQDQ and aarch64 SHA3/PMULL
semantics need explicit DOIT / PSTATE.DIT assumptions and actual runtime guards.
A disassembly rule scan is not an interprocedural leakage proof, and a function
call must not be treated as implicit vector cleanup.

**Verify your code, test your specs:** native `spec-oracle` differential and
clause-drop fuzzing, silicon cosimulation, `ct_dudect` and six-kernel
`comparator --paranoid` CI challenge replay complement the protocol/POSIX/QROM
and extracted-MIR pillars. Complete required-gate linkage to the exact release
binary remains an acceptance obligation. See [ASSURANCE.md](../ASSURANCE.md).


## 1. Overview & Security Goal

Source-level audits cannot rule out compiler-lowering hazards. `Qsag.ElfBinaryVerify`
checks selected compiled `libqsag_asm.rlib` fixture bytes inside Lean 4.35. This
narrows the gap for those symbols and contracts; it does not close the full
compiler, wrapper, dispatch or linked-executable boundary.
Specifically, the verification pipeline:
1. Parses `GNU ar` (`!<arch>\n`) archive headers and extended `//` filename tables in pure Lean 4 (`parseArArchive`, `parseArMember_subslice`).
2. Locates the `ELF64` relocatable object member (`.rcgu.o`), validates `Elf64_Ehdr`, `.shstrtab`, `.symtab`, `.strtab`, and `.text` `Elf64_Shdr` headers, and slices the exact `[st_value .. st_value + st_size)` machine bytes of every `STT_FUNC` symbol (`extractElfFuncBytes_in_text_section`).
3. Decodes all **23** exported cryptographic assembly kernels (**999** `x86_64` instructions + **299** `AArch64` instructions = **1,298** machine instructions) into operational semantics (`stepX86`/`runX86`, `stepArm64`/`runArm64`) with explicit leakage observations `StepObs` (`pc`, `(addr, width)` memory accesses, `isDoitSafe`).
4. Runs the relational abstract-origin & loop-invariant verifier `checkElfFuncThreeWayNI` (`O(1)` 3-level 16-way `PcMap` lookup) backed by the deductive soundness theorem **`checkElfFuncThreeWayNI_sound`**, discharging 3-way hardware constant-time noninterference (`PC-NI`, `Mem-NI`, `DOIT-NI`) plus System V AMD64 / AAPCS64 callee-saved preservation, `vzeroupper` hygiene, and scratch register zeroization before `ret`.
5. Supplies decoded-byte evidence for functional refinement work in `McRefine.lean`; complete byte-to-algebra coverage must be established per symbol, separately from noninterference.

---

## 2. Cryptographic Provenance of Verified `.rlib` Binaries

The table describes the embedded archives, which are historical (see the freshness result above); it is not a description of a current build. Both `.rlib` archives were compiled with `cargo build -p qsag-asm --release` (`release profile with LTO disabled`) on remote Linux hardware (`x86 Linux build host` for `x86_64`, `ARM Linux build host` for `aarch64`) and embedded as compact 32-word little-endian `UInt64` chunks in `lean/Qsag/CompiledRlibFixtures.lean` via `scripts/extract_rlib_elf.py`:

| Target Triple | Build Host | Artifact | Byte Size | SHA-256 Digest | Symbols / Instrs |
| :--- | :--- | :--- | ---: | :--- | ---: |
| `x86_64-unknown-linux-gnu` | `x86 Linux build host` | `libqsag_asm.rlib` | `499,610 B` | `7b7ec65deaa64bc7cc8392aaa417af7cdb011f6acd6e0001a5daac062b9937bf` | — |
| `x86_64-unknown-linux-gnu` | `x86 Linux build host` | `qsag_asm-*.rcgu.o` (`ELF64`, `EM_X86_64 = 62`) | `78,104 B` | `fbe87faf1486cb90698fba4dfd7497b66f50032a70d69abb7cddeaf1ee332702` | `16` (`999` instrs) |
| `aarch64-unknown-linux-gnu` | `ARM Linux build host` | `libqsag_asm.rlib` | `474,566 B` | `fa402d30bc323fa46d045c8717b143c5387f6d2372e3e45dff1ea31f1859e4bc` | — |
| `aarch64-unknown-linux-gnu` | `ARM Linux build host` | `qsag_asm-*.rcgu.o` (`ELF64`, `EM_AARCH64 = 183`) | `62,048 B` | `8ca2b4c1c28ee5d653803c2b4aa57681481179243f4addcc15eba797e3be8c7e` | `7` (`299` instrs) |

### Full 23-Symbol Inventory Verified by Kernel Reduction (`0 native_decide`)

#### `x86_64` (`16` symbols, `999` instructions — `rlib_x86_every_symbol_three_way_ni_sound`)
1. `qsag_asm_keccak_f1600_avx2_4x` (`0x0000..0x07f6`, 4-way AVX2 Keccak-$f[1600]$ with 32-byte aligned `0x340` stack frame, explicit 25-block `vmovdqa [rax], ymm0` stack scrub loop, `ymm0..ymm11` wipe, `vzeroupper`)
2. `qsag_asm_keccak_chi_mpc_avx2` (`0x0800`-aligned MPC $\chi$ gate over AVX2 shares)
3. `qsag_asm_gf256_shamir_mul_gfni` (`VGF2P8AFFINEQB` + `VGF2P8MULB` Wiedemann $\mathcal{T}_3$ multiplication, `ymm0..2, 14..15` wipe, `vzeroupper`)
4. `qsag_asm_gf256_shamir_mac_gfni` (`GFNI` Shamir MAC accumulation)
5. `qsag_asm_gf256_shamir_mul_avx2` (`VPSHUFB` split-nibble AVX2 fallback with public constant table `[r8 .. r8 + 0x80)`)
6. `qsag_asm_gf256_shamir_mac_avx2` (`VPSHUFB` split-nibble AVX2 Shamir MAC with public constant table `[r8 .. r8 + 0xa0)`)
7. `qsag_asm_tower128_bdoz_mac_vpclmul` (`AVX512DQ`/`AVX2` 256-bit `VPCLMULQDQ` $\mathcal{T}_7 \cong \mathbb{F}_{2^{128}}$ BDOZ MAC)
8. `qsag_asm_tower128_bdoz_mac_pclmul` (128-bit `VPCLMULQDQ` BDOZ MAC)
9. `qsag_asm_goldilocks_mul_ct_x86_64` (`BMI2` `MULX` + branchless `SBB` Goldilocks $p = 2^{64} - 2^{32} + 1$ multiplication)
10. `qsag_asm_goldilocks_add_ct_x86_64` (branchless 2-stage `SBB` Goldilocks addition)
11. `qsag_asm_goldilocks_sub_ct_x86_64` (branchless canonicalizing Goldilocks subtraction)
12. `qsag_asm_goldilocks_pow7_ct_x86_64` (`MULX` $x^7 \bmod p$ S-box power map with `r11` wipe)
13. `qsag_asm_goldilocks_dot2_adx_x86_64` (`BMI2`/`ADX` `MULX` + `ADCX`/`ADOX` 2-term inner product)
14. `qsag_asm_ct_eq_32_x86_64` (branchless 32-byte digest equality check with `rcx`, `rdx`, `r8` wipe)
15. `qsag_asm_ct_eq_bytes_x86_64` (branchless arbitrary-length byte-slice equality check with `r8`, `r9` wipe)
16. `qsag_asm_ct_memzero_x86_64` (looping byte wipe followed by `MFENCE` compiler/memory barrier)

#### `aarch64` (`7` symbols, `299` instructions — `rlib_aarch64_every_symbol_three_way_ni_sound`)
1. `qsag_asm_enable_dit_aarch64` (`MSR DIT, #1` + `ISB` hardware data-independent timing enablement)
2. `qsag_asm_keccak_sha3_neon` (`ARMv8.4-A+SHA3` `EOR` + `BCAX` 5-lane SIMD Keccak $\chi$ row with `v0..v7, v16..v20` wipe)
3. `qsag_asm_keccak_theta_rho_sha3_neon` (`EOR3` + `RAX1` + `XAR` Keccak $\theta + \rho$ step with `v0..v7, v16..v18` wipe)
4. `qsag_asm_tower128_bdoz_mac_pmull` (`PMULL`/`PMULL2` + `EXT` $\mathbb{F}_{2^{128}}$ BDOZ MAC with `v0..v7, v16..v20` wipe)
5. `qsag_asm_goldilocks_mul_ct_aarch64` (`MUL` + `UMULH` + `SUBS`/`ADDS`/`CSETM` branchless Goldilocks multiplication)
6. `qsag_asm_ct_eq_32_aarch64` (`LDP` + `EOR`/`ORR` + `CMP`/`CSET` 32-byte equality check with `x2..x7` wipe)
7. `qsag_asm_ct_memzero_aarch64` (`STRB` post-index wipe + `DMB ISH` barrier)

---

## 3. Core Theorems & Verification Guarantees (`lean/Qsag/ElfBinaryVerify.lean`)

### 3.1 Structural `GNU ar` & `ELF64` Parser Soundness (`§1–§2`)
- **`parseArMember_subslice`**: Every archive member returned by `parseArArchive` has exact length `m.payloadSize`, lies within `[0 .. rlib.size]`, and equals `(rlib.data.toList.drop m.payloadOffset).take m.payloadSize`.
- **`extractElfFuncBytes_in_text_section`**: Every symbol slice returned by `extractElfFuncBytes` has `slice.symSize > 0`, `slice.symValue + slice.symSize ≤ slice.textSize`, `slice.textFileOffset + slice.textSize ≤ elfBytes.length`, and `slice.code = (elfBytes.drop (slice.textFileOffset + slice.symValue)).take slice.symSize`.
- **`x86_rlib_symbol_names_exact` / `aarch64_rlib_symbol_names_exact`**: Kernel-decided discovery of all 16 `x86_64` and 7 `aarch64` symbols directly from the compiled `.rlib` byte streams.

### 3.2 3-Way Constant-Time Noninterference & ABI Hygiene (`§5`)
- **`checkElfFuncThreeWayNI_sound`**: If `checkElfFuncThreeWayNI elfBytes symName c = true`, then `symName` extracts cleanly from `.text` and for **any** two initial architectural states $(s_{1,0}, s_{2,0})$ satisfying the public-input contract `X86ContractInit c` / `Arm64ContractInit c` (agreeing on public pointers/lengths while arbitrary on all secret registers and secret memory) and **any** step bound `fuel`:
  1. **`PC-NI` + `Mem-NI` (`obs₁ = obs₂`)**: Every executed instruction emits the exact same program counter `pc` and the exact same sequence of `(effectiveAddress, byteWidth)` memory accesses (`0` secret-dependent branches, `0` secret-indexed LUT/cache accesses).
  2. **`DOIT-NI` (`obs.isDoitSafe = true`)**: Every executed instruction belongs strictly to the Intel DOITM / ARM `FEAT_DIT` constant-time whitelist (forbidding `div`/`idiv`/`udiv`/`sdiv`, `cl`-shifts, `lslv`/`lsrv`/`rorv`, `cbz`/`tbz`, `vpgather*`, indirect jumps, and register-offset loads/stores).
  3. **ABI & Epilogue Zeroization (`X86ExitHygiene` / `Arm64ExitHygiene`)**: Whenever execution reaches `ret` (`halted = true`), stack pointers and callee-saved registers (`rbx, rbp, r12..r15` on System V AMD64; `x19..x30, v8..v15` on AAPCS64) are restored, `ymmDirty = false` (`vzeroupper` executed), no scratch vector register holds `.secretVal`, and contract-mandated scratch GPRs are zeroed.
- **Non-Vacuity / Inhabitedness Witnesses (`x86_contract_init_inhabited`, `aarch64_contract_init_inhabited`)**: Constructively witness valid pairs of initial machine states satisfying `X86ContractInit` and `Arm64ContractInit` for non-aliasing public pointer contracts.

### 3.3 Negative Mutation Teeth (`§5a`)
Six kernel-checked negative mutation theorems prove that the analyzer actively rejects leaky or ABI-unhygienic machine code:
- `mutant_secret_branch_rejected`: Rejects `je` after secret `sub rax, rsi`.
- `mutant_secret_lut_rejected`: Rejects `[rdi + rsi*1]` secret table lookup.
- `mutant_variable_shift_rejected`: Rejects `x86_64` `shl rax, cl` and `AArch64` `lslv x0, x0, x1`.
- `mutant_udiv_rejected`: Rejects `x86_64` `div rsi` and `AArch64` `udiv x0, x0, x1`.
- `mutant_unwiped_neon_reg_rejected`: Patches `eor v16.16b, v16.16b, v16.16b` $\to$ `nop` at `+0x104` in real `qsag_asm_tower128_bdoz_mac_pmull` `.rlib` bytes and verifies rejection (`= false`).
- `mutant_missing_vzeroupper_rejected`: Patches `vzeroupper` $\to$ `nop; nop; nop` at `+0x72` in real `qsag_asm_gf256_shamir_mul_gfni` `.rlib` bytes and verifies rejection (`= false`).

### 3.4 Machine-code functional refinement

`lean/Qsag/McRefine.lean` is the functional bridge surface. A taint-checker
acceptance theorem does not prove that a kernel computes the intended field or
sponge operation. Complete byte-bound functional refinement for all production
symbols remains an integration obligation; consult the live declarations and
premises rather than extrapolating from the fixture inventory.

---

## 4. `LAW-M1` Encapsulation & Fast Kernel Elaboration Design

1. **Pinned fixture representation (`lean/Qsag/CompiledRlibFixtures.lean`):** Historical archive and object bytes are encoded in the source. The byte-pinned proofs quantify over this representation; current-source freshness is a separate, currently failing gate.
2. **Flat Register Banks & 3-Level Radix `PcMap` (`lean/Qsag/ElfBinaryVerify.lean`, `0` `@[expose]`):** `Bank16`, `Bank32`, and `PcMap` avoid `Array` bounds proof obligations and turn abstract-interpretation lookups into 3-step `O(1)` projections so kernel `decide +kernel` verifies all 1,298 instructions cleanly without `native_decide`.

---

## 5. Reproduction Commands (Remote Linux Hosts Only)

```bash
# 1. Standalone CLI inspection & cross-check of compiled .rlib archives
python3 scripts/extract_rlib_elf.py \
  --x86-rlib path/to/libqsag_asm_x86_64.rlib \
  --aarch64-rlib path/to/libqsag_asm_aarch64.rlib \
  --verify

# 2. From lean/ in an isolated Linux checkout with the matching toolchain
SWARM_MEM_MAX=12G timeout --kill-after=10s 600s swarm-build lake build Qsag.ElfBinaryVerify

# 3. Fixture freshness against a non-LTO build of the current source (prints a per-kernel verdict)
CARGO_PROFILE_RELEASE_LTO=false cargo build -p qsag-asm --release --target-dir target/ct-audit
CARGO_PROFILE_RELEASE_LTO=false cargo build -p qsag-asm --release \
  --target aarch64-unknown-linux-gnu --target-dir target/ct-audit
python3 scripts/audit_elf_ct.py --check-fixtures lean/Qsag/CompiledRlibFixtures.lean \
  --fixture-x86-rlib target/ct-audit/release/libqsag_asm.rlib \
  --fixture-aarch64-rlib target/ct-audit/aarch64-unknown-linux-gnu/release/libqsag_asm.rlib \
  --fixture-binding kernel-bytes

# 4. SyDTV cut discovery with z3 and Lean elaboration of the emitted proposals
python3 scripts/sydtv_driver.py --self-test --require-z3 --check-lean
```
