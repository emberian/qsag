#!/usr/bin/env python3
"""Refresh current archive literals and slices, preserving frozen challenge fixtures.

Use only artifacts built on the designated Linux host. The generated data are
untrusted proposals; ElfParse proves extraction and ElfFixtureVerify checks CT.
"""
import argparse
import hashlib
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts"))
import extract_rlib_elf as elf

def byte_list(data):
    return "[" + ", ".join(f"0x{x:02x}" for x in data) + "]"

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--x86-rlib", type=Path, required=True)
    ap.add_argument("--aarch64-rlib", type=Path, required=True)
    args = ap.parse_args()
    fixture = ROOT / "lean/Qsag/CompiledRlibFixtures.lean"
    slices = ROOT / "lean/Qsag/ElfFixtureSlices.lean"
    source = fixture.read_text()
    start = source.index("/-- Fresh Linux source build;")
    source = source[:start]
    normalized = slices.read_text()
    start = normalized.rfind("@[expose]", 0, normalized.index("def currentX86ExtractedSlices"))
    normalized = normalized[:start]
    bitslice_sha = hashlib.sha256((ROOT / "crates/qsag-asm/src/bitslice.rs").read_bytes()).hexdigest()
    for prefix, path, machine, count in [
        ("currentX86", args.x86_rlib, 62, 19),
        ("currentAarch64", args.aarch64_rlib, 183, 9),
    ]:
        digest, _, obj = elf.extract_qsag_elf_from_rlib(path)
        names = [x.name for x in obj.qsag_symbols]
        if obj.machine != machine or len(names) != count or len(set(names)) != count:
            raise ValueError(f"{prefix}: unexpected kernel inventory")
        archive = elf.build_deterministic_ar_single_elf(obj.member_name, obj.raw_bytes)
        source += f"/-- Fresh Linux source build; full rlib SHA-256 {digest}. -/\n"
        source += f"@[expose] noncomputable def {prefix}RlibLiteral : Nat × Nat :=\n"
        source += f"  ({len(archive)}, 0x{int.from_bytes(archive, 'little'):x})\n\n"
        for suffix, value in [
            ("RlibSha256", hashlib.sha256(archive).hexdigest()),
            ("RcguElfSha256", obj.sha256),
            ("BitsliceSourceSha256", bitslice_sha),
        ]:
            source += f'def {prefix}{suffix} : String := "{value}"\n\n'
        normalized += f"@[expose] def {prefix}ExtractedSlices : List ElfFuncSlice := [\n"
        rows = []
        for symbol in obj.qsag_symbols:
            rows.append(f'  {{ name := "{symbol.name}", nameBytes := {byte_list(symbol.name.encode())}\n'
                        f'    machine := {obj.machine}, textFileOffset := {obj.text_offset}, textSize := {obj.text_size}\n'
                        f'    symValue := {symbol.value}, symSize := {symbol.size}\n'
                        f'    code := {byte_list(symbol.code)} }}')
        normalized += ",\n".join(rows) + "\n]\n\n"
        print(f"{prefix}: {count} pinned symbols, object SHA-256 {obj.sha256}")
    fixture.write_text(source + "end Qsag\nend\n")
    slices.write_text(normalized + "end Qsag\n")

if __name__ == "__main__":
    main()

