#!/usr/bin/env python3
"""Capture fresh ELF evidence; this does not generate Lean certificates.

Run on the Linux build host after the two non-LTO qsag-asm builds.
The archive parser and instruction auditor remain the repository's existing tools.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import struct
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts"))
import extract_rlib_elf as elf


def sha(data):
    return hashlib.sha256(data).hexdigest()


def linked_kernels(data):
    """Extract STT_FUNC bytes from the final x86 ELF using section virtual addresses."""
    def region(offset, size):
        if not 0 <= offset <= len(data) or not 0 <= size <= len(data) - offset:
            raise ValueError("ELF range outside file")
        return data[offset:offset + size]

    header = struct.unpack("<16sHHIQQQIHHHHHH", region(0, 64))
    ident, kind, machine, _, _, _, shoff, _, _, _, _, entsize, count, _ = header
    if ident[:6] != b"\x7fELF\x02\x01" or kind not in (2, 3) or machine != 62 or entsize != 64:
        raise ValueError("expected linked little-endian x86 ELF64")
    sections = [struct.unpack("<IIQQQQIIQQ", region(shoff + i * 64, 64)) for i in range(count)]
    kernels = {}
    for section in sections:
        if section[1] != 2:
            continue
        if section[9] != 24 or section[5] % 24 or section[6] >= count:
            raise ValueError("invalid symbol table")
        strings = sections[section[6]]
        strings = region(strings[4], strings[5])
        for offset in range(section[4], section[4] + section[5], 24):
            name, info, _, index, value, size = struct.unpack("<IBBHQQ", region(offset, 24))
            if info & 15 != 2 or index == 0:
                continue
            if name >= len(strings) or strings.find(b"\0", name) < 0:
                raise ValueError("invalid symbol name")
            name = strings[name:strings.index(b"\0", name)].decode()
            if not name.startswith("qsag_asm_"):
                continue
            if index >= count or name in kernels or size == 0:
                raise ValueError("invalid kernel symbol")
            target = sections[index]
            relative = value - target[3]
            if target[1] != 1 or relative < 0 or relative + size > target[5]:
                raise ValueError("kernel outside section")
            code = region(target[4] + relative, size)
            kernels[name] = {"name": name, "address": value, "size": size,
                             "sha256": sha(code), "hex": code.hex()}
    return kernels


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--x86-rlib", type=Path, required=True)
    parser.add_argument("--aarch64-rlib", type=Path, required=True)
    parser.add_argument("--objdump", required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--linked-x86", type=Path)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    manifest = {
        "schema": 1,
        "certificate_status": "uncertified; production Lean fixtures unchanged",
        "rustc": subprocess.check_output(["rustc", "-Vv"], text=True),
        "objdump": subprocess.check_output([args.objdump, "--version"], text=True),
        "source_sha256": {},
        "architectures": {},
    }
    sources = [ROOT / p for p in ("Cargo.toml", "Cargo.lock", "rust-toolchain.toml")]
    sources += sorted((ROOT / "crates/qsag-asm").rglob("*.rs"))
    sources += sorted((ROOT / "crates/qsag-asm").rglob("*.s"))
    sources += [ROOT / "crates/qsag-asm/Cargo.toml", ROOT / "scripts/extract_rlib_elf.py",
                Path(__file__).resolve()]
    for path in sources:
        manifest["source_sha256"][str(path.relative_to(ROOT))] = sha(path.read_bytes())
    for arch, machine, archive in [("x86_64", 62, args.x86_rlib),
                                   ("aarch64", 183, args.aarch64_rlib)]:
        archive_sha, archive_size, obj = elf.extract_qsag_elf_from_rlib(archive)
        if obj.machine != machine:
            raise ValueError(f"wrong architecture for {archive}")
        names = [s.name for s in obj.qsag_symbols]
        if not names or len(names) != len(set(names)):
            raise ValueError("empty or duplicate kernel inventory")
        object_path = args.output / f"{arch}.o"
        object_path.write_bytes(obj.raw_bytes)
        (args.output / f"{arch}.rlib").write_bytes(archive.read_bytes())
        options = ["-M", "intel"] if machine == 62 else ["--mattr=+v8.4a,+sha3,+aes,+dit"]
        disasm = subprocess.check_output([args.objdump, "-d", *options, str(object_path)], text=True)
        # Avoid embedding an absolute output directory in the disassembly header.
        disasm = disasm.replace(str(object_path), object_path.name)
        (args.output / f"{arch}.disasm").write_text(disasm)
        manifest["architectures"][arch] = {
            "build_command": "CARGO_PROFILE_RELEASE_LTO=false cargo build -p qsag-asm --release "
                             f"--target {arch}-unknown-linux-gnu --target-dir target/ct-audit",
            "archive_sha256": archive_sha, "archive_size": archive_size,
            "object_member": obj.member_name, "object_sha256": obj.sha256,
            "object_size": len(obj.raw_bytes), "machine": machine,
            "disassembly_sha256": sha(disasm.encode()),
            "kernels": [{"name": s.name, "offset": s.value, "size": s.size,
                         "sha256": sha(s.code), "hex": s.code.hex()}
                        for s in obj.qsag_symbols],
        }
    if args.linked_x86:
        data = args.linked_x86.read_bytes()
        linked = linked_kernels(data)
        original = {s["name"]: s for s in manifest["architectures"]["x86_64"]["kernels"]}
        if linked.keys() != original.keys():
            raise ValueError("linked and archive kernel inventories differ")
        for name, symbol in linked.items():
            if symbol["hex"] != original[name]["hex"]:
                raise ValueError(f"linked kernel bytes differ: {name}")
        command = [args.objdump, "-d", "-M", "intel",
                   "--disassemble-symbols=" + ",".join(linked), str(args.linked_x86)]
        disasm = subprocess.check_output(command, text=True).replace(str(args.linked_x86), "qsag-thinlto")
        (args.output / "x86_64-thinlto.disasm").write_text(disasm)
        manifest["linked_x86"] = {
            "sha256": sha(data), "size": len(data), "kernels": list(linked.values()),
            "archive_kernel_bytes_identical": True, "disassembly_sha256": sha(disasm.encode()),
            "build_command": "CARGO_PROFILE_RELEASE_LTO=thin CARGO_PROFILE_RELEASE_STRIP=none "
                             "cargo build --release --offline -p qsag-cli --target-dir target/ct-linked",
        }
        print(f"ThinLTO: all {len(linked)} kernels byte-identical to the fresh archive")
    (args.output / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    for arch, item in manifest["architectures"].items():
        print(f"{arch}: captured {len(item['kernels'])} kernels; {item['object_sha256']}")


if __name__ == "__main__":
    main()
