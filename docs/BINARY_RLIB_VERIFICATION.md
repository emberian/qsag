# Binary / ELF verification status

## Wave-4b result

**Freshness and constant-time certificate gate: 28/28. Whole-kernel functional
gate: 12/28; incomplete.** This is not a claim of complete production functional
equivalence.

The `currentX86…` and `currentAarch64…` fixtures contain new full native ELF
members built on the designated Linux build host from the source snapshot recorded in
[`wave4b-elf/manifest.json`](../lean/fixtures/wave4b-elf/manifest.json).
Both object binding and per-symbol binding match the live rebuild: **19/19
x86_64 and 9/9 AArch64**, zero changed, removed, or unpinned exported kernels.
The recheck includes the other lane's new Rust scale-XOR implementation.
Its inline assembly is outside the 28 `qsag_asm_*` symbols and has no certificate
here.

- `ElfParse` proves exact archive extraction and in-bounds provenance for every
  fresh slice. Digest comparison is an external freshness check, not a Lean axiom.
- `ElfFixtureVerify.currentX86_rlib_every_symbol_three_way_ni_sound` and
  `currentAarch64_rlib_every_symbol_three_way_ni_sound` cover every fresh symbol,
  with the existing relational CT, ABI, vector-cleanup and scratch contracts.
- The decoder now supports AArch64 paired Q loads/stores, DUP .2D, AND .16B,
  SHL .2D and USHR .2D. The concrete executor and abstract transfer function
  are connected by the updated instruction soundness proof. USHR #64 is
  explicitly zero-producing; duplicate paired-load destinations and unsupported
  SP addressing fail closed.
- The PC map covers 8,192 bytes. Its former 4,096-byte limit could not represent
  the 4,264-byte AArch64 transpose. Bounds and map lookup proofs were updated.
- The 28 fresh certificates share 476 abstract states. Untrusted inference
  proposes these states; each certificate is checked by kernel reduction.
  Regeneration tools are in [the fixture directory](../lean/fixtures/README.md).
- Fresh negative controls reject the historical scalar certificate, removed
  GFNI vector cleanup, removed PMULL vector wiping, and a tampered digest.

The modeled timing guarantees retain their hardware/environment assumptions,
including DOIT/DIT where required. They are not interprocedural, wrapper,
whole-process, or physical timing proofs. Archive freshness alone does not
certify compiled Rust functions, dispatch, or the final executable.

## Why the historical API remains

`QsagChallenge.lean`, `Qsag/Apex.lean` and `lean/comparator.json` are unchanged.
Their old fixture names remain historical compatibility APIs.

Some frozen theorem signatures are false for the live bytes. For example,
`ct_eq_32_x86_64_mc_refines` promises termination at fuel 20; the live equality
kernel has 28 instructions. `McRefine.current_ct_eq_32_requires_new_budget`
kernel-checks a counterexample at fuel 20. The fresh versions use separately
named `current_…` theorems and the correct budgets; neither the executor's step
meaning nor the old statements were weakened.

The auditor therefore requires explicit `--fixture-generation current` for
the fresh gate. Its default remains `historical`, so old consumers cannot
silently change which archive they audit.

## Functional coverage and outstanding work

Every row below has a fresh byte binding, complete decode and CT certificate.
“Proved” means a fresh-byte whole-kernel result in `McRefine` /
`ElfFunctionalEquiv`; “Open” means the mathematical refinement is still missing.
Instruction screening, normalized decoding, simulator agreement and CT
acceptance are not counted as functional equivalence.

| Architecture | Export (prefix `qsag_asm_`) | Instructions | Functional |
| --- | --- | ---: | --- |
| x86_64 | `keccak_f1600_avx2_4x` | 309 | Open |
| x86_64 | `keccak_chi_mpc_avx2` | 74 | Open |
| x86_64 | `gf256_shamir_mul_gfni` | 35 | Proved |
| x86_64 | `gf256_shamir_mac_gfni` | 40 | Open |
| x86_64 | `gf256_shamir_mul_avx2` | 121 | Open |
| x86_64 | `gf256_shamir_mac_avx2` | 135 | Open |
| x86_64 | `tower128_bdoz_mac_vpclmul` | 52 | Open |
| x86_64 | `tower128_bdoz_mac_pclmul` | 76 | Open |
| x86_64 | `goldilocks_mul_ct_x86_64` | 33 | Proved |
| x86_64 | `goldilocks_add_ct_x86_64` | 25 | Proved |
| x86_64 | `goldilocks_sub_ct_x86_64` | 31 | Proved |
| x86_64 | `goldilocks_pow7_ct_x86_64` | 93 | Open |
| x86_64 | `goldilocks_dot2_adx_x86_64` | 52 | Open |
| x86_64 | `ct_eq_32_x86_64` | 28 | Proved |
| x86_64 | `ct_eq_bytes_x86_64` | 23 | Proved |
| x86_64 | `ct_memzero_x86_64` | 17 | Proved |
| x86_64 | `transpose64x256_avx2` | 685 | Open |
| x86_64 | `gf2_128_mul_acc_pclmul` | 50 | Open |
| x86_64 | `gf2_128_mul_acc_vpclmul` | 56 | Open |
| aarch64 | `enable_dit_aarch64` | 3 | Proved |
| aarch64 | `keccak_sha3_neon` | 39 | Proved |
| aarch64 | `keccak_theta_rho_sha3_neon` | 128 | Open |
| aarch64 | `tower128_bdoz_mac_pmull` | 73 | Open |
| aarch64 | `goldilocks_mul_ct_aarch64` | 30 | Proved |
| aarch64 | `ct_eq_32_aarch64` | 22 | Proved |
| aarch64 | `ct_memzero_aarch64` | 5 | Proved |
| aarch64 | `transpose64x256_neon` | 1066 | Open |
| aarch64 | `gf2_128_mul_acc_pmull` | 54 | Open |

Fresh functional results cover Goldilocks add/subtract/multiply on x86_64,
Goldilocks multiply on AArch64, fixed-size equality on both architectures,
variable-size equality on x86_64, memory wiping on both architectures,
AArch64 DIT enablement and Keccak χ, and GFNI tower multiplication.
The GFNI loop theorem retains its nonzero-count, address-bound and input/output
disjointness premises for the multi-block mathematical result. The memory and
variable-equality kernels retain their positive-count premises; wrapper early
returns are not decoded kernel execution.

**Outstanding vertical work (owned, not awaiting file permission):**

1. Prove fresh full-kernel mathematical refinement for the 16 “Open” rows:
   x86_64 Keccak-f1600 and MPC χ; GFNI MAC; both AVX2 Shamir kernels; both
   tower128 MAC kernels; Goldilocks pow7 and dot2; both transposes; and all three
   GF2 multiply-accumulate kernels; AArch64 theta/rho and tower128 MAC.
2. Connect the new inline `poly_scale_xor_x86` routine to an explicit byte-bound
   certificate and polynomial-field specification. It is outside the exported
   assembly inventory.
3. Migrate remaining historical SyDTV/functional consumers to fresh APIs as their
   functional obligations are discharged. Existing guarded zero-count runners
   remain models of wrappers.
4. Runtime shader functional equivalence remains unproved. The SPIR-V module
   proves codec, scheduling, race-freedom and leakage-model properties.

These are proof/integration gaps. Passing the build and axiom census does not
close them.

## Validation evidence

All compilers ran on the designated Linux build host in an isolated checkout, seeded from
a warm convergence cache, under
`SWARM_MEM_MAX=12G timeout --kill-after=10s 600s swarm-build`.
No macOS compilation or `/dev/shm` was used. Hostnames and checkout prefixes
in retained textual logs are redacted; binary artifacts are unchanged.

- [Freshness, object binding](../lean/fixtures/w4b-freshness-final.log):
  19/19 + 9/9; both complete native object digests identical.
- [Instruction screens](../lean/fixtures/w4b-instruction-screen-final.log):
  both current archives; 34 auditor self-tests.
- [13-module warning-free build](../lean/fixtures/w4b-build-final.log).
- [Axiom census](../lean/fixtures/w4b-axioms-final.log): direct `import all`
  of all 13 modules, `setExporting false`, `Lean.collectAxioms`, and a negative
  control. 11,609 declarations and 6,410 theorems checked, zero rejected.
  Only `propext` and `Quot.sound` are allowed.
- [Challenge build](../lean/fixtures/w4b-challenge-final.log):
  unchanged signatures; intentional challenge-hole warnings are expected.
- [Source policy](../lean/fixtures/w4b-policy-final.log):
  no proof escapes and at most 12 `@[expose]` annotations per file.
  The isolated snapshot passes. The current shared checkout additionally reports two
  outside-scope file-wide exposure violations in generated MIR files; see
  [the local policy report](../lean/fixtures/w4b-local-policy-final.log).
  The external `scan_badwords.py` cleanliness check is recorded separately in
  [the cleanliness report](../lean/fixtures/w4b-cleanliness-final.log); outside-scope findings
  are not part of the proof-policy result.
- [SyDTV checks](../lean/fixtures/w4b-sydtv-final.log):
  self-tests, Z3 cuts and emitted Lean certificate proposals. These still test
  the historical SyDTV API.

The prior [Wave-4 evidence](../lean/fixtures/wave4-elf/manifest.json), including
19/19 matching ThinLTO symbol bytes, is retained as historical evidence.
Wave-4b does not claim a newly linked executable or a new native silicon run.

## Reproduction

```sh
# Build on the designated Linux build host using the pinned Rust toolchain.
SWARM_MEM_MAX=12G timeout --kill-after=10s 600s swarm-build \
  env CARGO_PROFILE_RELEASE_LTO=false cargo build -p qsag-asm --release \
  --target x86_64-unknown-linux-gnu --target-dir target/ct-audit
SWARM_MEM_MAX=12G timeout --kill-after=10s 600s swarm-build \
  env CARGO_PROFILE_RELEASE_LTO=false cargo build -p qsag-asm --release \
  --target aarch64-unknown-linux-gnu --target-dir target/ct-audit

python3 scripts/audit_elf_ct.py \
  --check-fixtures lean/Qsag/CompiledRlibFixtures.lean \
  --fixture-generation current --fixture-binding object \
  --fixture-x86-rlib target/ct-audit/x86_64-unknown-linux-gnu/release/libqsag_asm.rlib \
  --fixture-aarch64-rlib target/ct-audit/aarch64-unknown-linux-gnu/release/libqsag_asm.rlib

# From lean/, after the library build:
SWARM_MEM_MAX=12G timeout --kill-after=10s 600s swarm-build \
  lake env lean fixtures/AuditVertical.lean
```

If build paths or compiled Rust code change while exported assembly bytes remain
identical, `--fixture-binding kernel-bytes` checks exact symbol-set and byte
equality without requiring unrelated object bytes to match. Neither mode may
be represented as certifying symbols outside the pinned inventory.
