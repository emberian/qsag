# Binary / ELF verification

**Fresh byte binding and constant-time certificates: 28/28. Whole-kernel
mathematical refinement: 26/28.** The two transpose kernels remain open.

The current fixture APIs bind the 19 x86-64 and nine AArch64 exported assembly
symbols to native ELF members in [CompiledRlibFixtures.lean](../lean/Qsag/Machine/CompiledRlibFixtures.lean)
and [ElfFixtureSlices.lean](../lean/Qsag/Machine/ElfFixtureSlices.lean). Digests are
external freshness checks, not Lean axioms.

## Functional coverage

“Proved” means fresh bytes, a kernel-checked decode equation, execution from an
arbitrary state satisfying explicit preconditions, and a mathematical result.
Decoder acceptance, constant-time certificates and silicon agreement alone do
not count as functional equivalence.

| Architecture | Export (prefix `qsag_asm_`) | Instructions | Functional |
| --- | --- | ---: | --- |
| x86_64 | `keccak_f1600_avx2_4x` | 309 | Proved |
| x86_64 | `keccak_chi_mpc_avx2` | 74 | Proved |
| x86_64 | `gf256_shamir_mul_gfni` | 35 | Proved |
| x86_64 | `gf256_shamir_mac_gfni` | 40 | Proved |
| x86_64 | `gf256_shamir_mul_avx2` | 121 | Proved |
| x86_64 | `gf256_shamir_mac_avx2` | 135 | Proved |
| x86_64 | `tower128_bdoz_mac_vpclmul` | 52 | Proved |
| x86_64 | `tower128_bdoz_mac_pclmul` | 76 | Proved |
| x86_64 | `goldilocks_mul_ct_x86_64` | 33 | Proved |
| x86_64 | `goldilocks_add_ct_x86_64` | 25 | Proved |
| x86_64 | `goldilocks_sub_ct_x86_64` | 31 | Proved |
| x86_64 | `goldilocks_pow7_ct_x86_64` | 93 | Proved |
| x86_64 | `goldilocks_dot2_adx_x86_64` | 52 | Proved |
| x86_64 | `ct_eq_32_x86_64` | 28 | Proved |
| x86_64 | `ct_eq_bytes_x86_64` | 23 | Proved |
| x86_64 | `ct_memzero_x86_64` | 17 | Proved |
| x86_64 | `transpose64x256_avx2` | 685 | Open |
| x86_64 | `gf2_128_mul_acc_pclmul` | 50 | Proved |
| x86_64 | `gf2_128_mul_acc_vpclmul` | 56 | Proved |
| aarch64 | `enable_dit_aarch64` | 3 | Proved |
| aarch64 | `keccak_sha3_neon` | 39 | Proved |
| aarch64 | `keccak_theta_rho_sha3_neon` | 128 | Proved |
| aarch64 | `tower128_bdoz_mac_pmull` | 73 | Proved |
| aarch64 | `goldilocks_mul_ct_aarch64` | 30 | Proved |
| aarch64 | `ct_eq_32_aarch64` | 22 | Proved |
| aarch64 | `ct_memzero_aarch64` | 5 | Proved |
| aarch64 | `transpose64x256_neon` | 1066 | Open |
| aarch64 | `gf2_128_mul_acc_pmull` | 54 | Proved |

The new Goldilocks pow7 and dot2 results include complete execution, the modular
field result, callee-saved preservation, memory framing and scratch-register
wiping. GFNI MAC and both AVX2 Shamir loops cover every positive count under
explicit address bounds and source/output separation. AVX2 premises describe
the actual table vectors loaded, with bytewise bridges to BinaryTower products.

Keccak MPC χ covers all five output vectors and reconstructs three shares to
χ across all four packed rows. NEON θ/ρ includes π and covers both complete
25-lane states. The four-state permutation executes all 24 rounds and cleanup;
its theorem uses the canonical public round table and explicit state, table,
scratch and saved-frame separation premises.

All six GF(2^128) kernels refine independent schoolbook polynomial multiplication
and long division modulo z^128 + z^7 + z^2 + z + 1. Their count is positive;
VPCLMUL multiply-accumulate counts pairs. Stores follow input reads, so these
results allow input/output aliasing. The SyDTV accumulator identity covers both
packed lanes and every algebraic block count.

## Decoder and translation-validation boundaries

- AArch64 ASR sign-extends; invalid add/sub shift kinds and oversized 32-bit
  shifts are rejected. CSEL/CSINV preserve the sf width and zero-extend W writes.
  SP-addressing forms are rejected rather than interpreted as XZR. Modeling
  general SP execution remains outside the supported instruction subset.
- DIT is an explicit caller contract assumption. A kernel that establishes DIT
  can start without that assumption. These are conditional timing-model results,
  not observations of physical processor timing.
- x86 F2-prefixed unsupported forms and legacy/REX prefixes before VEX are
  rejected. Accepted instructions are at most 15 bytes. VEX.L controls broadcast
  width. Frame contracts require the full 800-byte Keccak spill region to be
  zero on return after the 832-byte allocation.
- SyDTV's zero-count VPCLMUL wrapper model preserves memory and emits no memory
  access. It does not claim raw zero-count assembly execution. Both SIMD
  postconditions preserve r12–r15 as well as the other callee-saved registers.
- The five loop certificates also produce flattened cut-graph refinement proofs.
  Graph nodes execute the same certified cut steps connected to decoded
  instructions by the replay lemmas. The field postcondition follows from the
  independent GF(2^128) identity.
- The Python SyDTV driver defaults to current fixtures. It checks relocation
  write intervals, rejects overlaps or unknown kinds, and emits byte-bound Lean
  proposals for current memzero kernels, including rebuilt Rust archives with
  function-free metadata members. Python/Z3 results remain untrusted
  until the generated declaration elaborates.

## Validation and remaining work

`scripts/isa_cosim_silicon.py` selects all 19 x86-64 exports. Variable-count
kernels cover zero, one, two, three and a page-crossing count, and zero cases
execute the actual Rust wrappers (3,349 instruction probes plus independent ABI
checks, with zero register, memory, defined-flag or PC-trace mismatches).

The warning-free ten-module build and axiom census (`import all` +
`setExporting false` + `Lean.collectAxioms`, permitting only `propext` and
`Quot.sound`) check 8,673 declarations, including 5,420 theorems, with zero
rejected axioms. Registered mutation teeth and inhabitedness witnesses audit the
refinement, decoding and provenance claims.

Outstanding work:

1. Whole-kernel mathematical refinement for both 64×256 transpose kernels.
2. Native positive-count silicon coverage on hardware with GFNI/VPCLMULQDQ.
3. AArch64 silicon co-simulation; the current native harness is x86-64.
4. The inline Rust scale-XOR routine is outside the 28 exported assembly symbols.
5. Historical SyDTV APIs remain compatibility models; their wrapper guard is
   explicit. Full compiled-wrapper refinement and final linked-executable
   coverage are separate obligations.

This work leaves `QsagChallenge.lean` and `Qsag/Top/Apex.lean` untouched. Historical names retain historical bytes and budgets. For example,
the current fixed-size x86 equality kernel needs 28 instructions, so the old
20-step theorem cannot describe it; the current APIs state the correct budget.

## Reproduction

Run the builds on a Linux host with a memory limit in place (the commands below were
sized for 12 GiB and six Lean threads). From the repository root:

```sh
CARGO_PROFILE_RELEASE_LTO=false cargo build -p qsag-asm --release \
  --target x86_64-unknown-linux-gnu --target-dir target/ct-audit
CARGO_PROFILE_RELEASE_LTO=false cargo build -p qsag-asm --release \
  --target aarch64-unknown-linux-gnu --target-dir target/ct-audit
python3 scripts/audit_elf_ct.py --fixture-generation current \
  --check-fixtures lean/Qsag/Machine/CompiledRlibFixtures.lean --fixture-binding kernel-bytes \
  --fixture-x86-rlib target/ct-audit/x86_64-unknown-linux-gnu/release/libqsag_asm.rlib \
  --fixture-aarch64-rlib target/ct-audit/aarch64-unknown-linux-gnu/release/libqsag_asm.rlib
python3 scripts/sydtv_driver.py --self-test --require-z3 --check-lean
python3 scripts/isa_cosim_silicon.py --count 128 \
  --kernel-elf target/ct-audit/x86_64-unknown-linux-gnu/release/libqsag_asm.rlib
python3 scripts/check_lean_policy.py
cd lean
LEAN_NUM_THREADS=6 \
  lake build --wfail Qsag.Machine.CompiledRlibFixtures Qsag.Machine.ElfFixtureSlices \
  Qsag.Machine.ElfInvCerts Qsag.Machine.ElfParse Qsag.Machine.McRefine \
  Qsag.Machine.ElfBinaryVerify Qsag.Machine.ElfFixtureVerify \
  Qsag.Machine.ElfFunctionalEquiv Qsag.Machine.SydTvTranslationValidation Qsag.Machine.IsaCosim
LEAN_NUM_THREADS=6 \
  lake env lean fixtures/AuditVertical.lean
```

Use explicit archive paths after rebuilding; binary dumps and transient logs
are not retained in the source tree. Legacy manifest aliases remain for tools
with frozen fixture-directory names. The auditor's default generation remains
historical, so selecting current bytes must be explicit.
