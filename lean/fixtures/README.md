# ELF fixtures and certificates

Current fixtures bind all 19 x86-64 and nine AArch64 exported assembly kernels.
All 28 have constant-time certificates; 26 have fresh whole-kernel mathematical
refinement. See [the scope and remaining work](../../docs/BINARY_RLIB_VERIFICATION.md).

`current-elf/manifest.json` records the current source capture.
`historical-elf/manifest.json` records the predecessor capture. Rebuild archives and
pass explicit paths to the auditor; transient logs and binary dumps are omitted.

## Regenerating the current certificates

Build both `qsag-asm` archives on an x86-64/AArch64 Linux host using the commands in the
verification document. Then, from the checkout root:

```sh
python3 lean/fixtures/refresh_current_fixtures.py \
  --x86-rlib target/ct-audit/x86_64-unknown-linux-gnu/release/libqsag_asm.rlib \
  --aarch64-rlib target/ct-audit/aarch64-unknown-linux-gnu/release/libqsag_asm.rlib
cd lean
lake build --wfail Qsag.Machine.ElfBinaryVerify
task_tmpdir=$(mktemp -d)
lake env lean --run fixtures/GenerateCurrentInvs.lean "$task_tmpdir/proposals.inc"
python3 fixtures/install_current_invariants.py "$task_tmpdir/proposals.inc"
rm -rf "$task_tmpdir"
lake build --wfail Qsag.Machine.ElfFixtureVerify Qsag.Machine.McRefine Qsag.Machine.ElfFunctionalEquiv
lake env lean fixtures/AuditVertical.lean
```

The emitters are untrusted. The archive parser proves the byte binding and the
kernel checks each proposed invariant. Equal abstract states are interned to
keep elaboration fast. Changes to symbol count, code, contracts or semantics
can require updating the proof declarations; regeneration does not bypass them.

Freshness selection is explicit:

```sh
python3 scripts/audit_elf_ct.py \
  --check-fixtures lean/Qsag/Machine/CompiledRlibFixtures.lean \
  --fixture-generation current --fixture-binding object \
  --fixture-x86-rlib target/ct-audit/x86_64-unknown-linux-gnu/release/libqsag_asm.rlib \
  --fixture-aarch64-rlib target/ct-audit/aarch64-unknown-linux-gnu/release/libqsag_asm.rlib
```

Use `kernel-bytes` instead of `object` when unrelated native Rust code or build
paths change while the exact exported symbol inventory and machine bytes stay
identical. The default generation is historical, for API compatibility.


`capture_elf.py` captures evidence and checks linked/relocatable bytes when
`--linked-x86` is supplied. Capturing artifacts alone does not certify them.
