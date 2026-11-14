# ELF fixtures and certificates

Wave-4b pins all **19 x86_64 + 9 AArch64** exported assembly kernels in the
`current…` archive/slice APIs. All 28 have kernel-checked CT certificates.
Fresh whole-kernel functional refinement covers **12/28**; the remaining
16 are listed in [BINARY_RLIB_VERIFICATION.md](../../docs/BINARY_RLIB_VERIFICATION.md).
The frozen historical fixture APIs remain for unchanged Apex/Challenge signatures.

`wave4b-elf/` contains the archives, objects, disassembly and source manifest
for the final Linux rebuild, including the concurrent scale-XOR source addition.
That inline routine is not one of the 28 exported symbols and is not certified.
`w4b-*-final.log` files record the validation gates. The exact scope of each
gate is documented beside the inventory.

## Regenerating the current certificates

Run all compilers on the designated Linux build host. Build both qsag-asm archives using the commands in the
verification document. Then, from the checkout root:

```sh
python3 lean/fixtures/refresh_current_fixtures.py \
  --x86-rlib target/ct-audit/x86_64-unknown-linux-gnu/release/libqsag_asm.rlib \
  --aarch64-rlib target/ct-audit/aarch64-unknown-linux-gnu/release/libqsag_asm.rlib
cd lean
SWARM_MEM_MAX=12G timeout --kill-after=10s 600s swarm-build \
  lake build --wfail Qsag.ElfBinaryVerify
task_tmpdir=$(mktemp -d)
SWARM_MEM_MAX=12G timeout --kill-after=10s 600s swarm-build \
  lake env lean --run fixtures/GenerateCurrentInvs.lean "$task_tmpdir/proposals.inc"
python3 fixtures/install_current_invariants.py "$task_tmpdir/proposals.inc"
rm -rf "$task_tmpdir"
SWARM_MEM_MAX=12G timeout --kill-after=10s 600s swarm-build \
  lake build --wfail Qsag.ElfFixtureVerify Qsag.McRefine Qsag.ElfFunctionalEquiv
SWARM_MEM_MAX=12G timeout --kill-after=10s 600s swarm-build \
  lake env lean fixtures/AuditVertical.lean
```

The emitters are untrusted. The archive parser proves the byte binding and the
kernel checks each proposed invariant. Equal abstract states are interned to
keep elaboration fast. Changes to symbol count, code, contracts or semantics
can require updating the proof declarations; regeneration does not bypass them.

Freshness selection is explicit:

```sh
python3 scripts/audit_elf_ct.py \
  --check-fixtures lean/Qsag/CompiledRlibFixtures.lean \
  --fixture-generation current --fixture-binding object \
  --fixture-x86-rlib target/ct-audit/x86_64-unknown-linux-gnu/release/libqsag_asm.rlib \
  --fixture-aarch64-rlib target/ct-audit/aarch64-unknown-linux-gnu/release/libqsag_asm.rlib
```

Use `kernel-bytes` instead of `object` when unrelated native Rust code or build
paths change while the exact exported symbol inventory and machine bytes stay
identical. The default generation is historical, for API compatibility.

## Prior Wave-4 capture

`wave4-elf/` is preserved evidence from the predecessor. At capture time these
artifacts had no fresh CT certificates. Its manifest includes a ThinLTO
comparison: all 19 linked x86 kernels matched the relocatable bodies.
No new ThinLTO link or native silicon comparison is claimed by Wave-4b.

The old `decoder-probe.log` records the then-missing AArch64 transpose decoder.
Wave-4b adds those semantics and expands the PC map, so the old failure is
historical. Its baseline build, axiom, challenge and SyDTV logs likewise refer
to the earlier fixture API.

`capture_elf.py` captures evidence and checks linked/relocatable bytes when
`--linked-x86` is supplied. Capturing artifacts alone does not certify them.

