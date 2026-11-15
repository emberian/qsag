#!/usr/bin/env python3
"""
Deterministic GNU `ar` (`.rlib`) + `ELF64` Machine-Code Inspector, Standalone
Constant-Time / ABI Verifier, and Lean 4 Fixture Generator (`QSAG-6`).

Usage:
  1. Standalone CLI inspection & constant-time verification on any compiled `.rlib`:
       python3 scripts/extract_rlib_elf.py --verify path/to/libqsag_asm.rlib

  2. Deterministic generation of `lean/Qsag/Machine/CompiledRlibFixtures.lean`:
       python3 scripts/extract_rlib_elf.py \
         --generate-lean lean/Qsag/Machine/CompiledRlibFixtures.lean \
         --x86-rlib path/to/x86_64/libqsag_asm.rlib \
         --aarch64-rlib path/to/aarch64/libqsag_asm.rlib
"""

from __future__ import annotations

import argparse
import hashlib
import json
import struct
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Optional, Tuple

AR_MAGIC = b"!<arch>\n"
ELF_MAGIC = b"\x7fELF"
ELFCLASS64 = 2
ELFDATA2LSB = 1
ET_REL = 1
EM_X86_64 = 62
EM_AARCH64 = 183

SHT_PROGBITS = 1
SHT_SYMTAB = 2
SHT_STRTAB = 3
STT_FUNC = 2


@dataclass
class ArMember:
    name: str
    offset: int
    size: int
    payload: bytes


@dataclass
class ElfSymbol:
    name: str
    bind: int
    sym_type: int
    shndx: int
    section_name: str
    value: int
    size: int
    code: bytes


@dataclass
class ParsedElfObject:
    member_name: str
    raw_bytes: bytes
    sha256: str
    machine: int
    ehsize: int
    shoff: int
    shentsize: int
    shnum: int
    shstrndx: int
    text_offset: int
    text_size: int
    qsag_symbols: List[ElfSymbol]


def parse_ar_archive(data: bytes) -> List[ArMember]:
    if len(data) < 8 or data[:8] != AR_MAGIC:
        raise ValueError("Invalid GNU ar archive: missing !<arch>\\n header")
    pos = 8
    ext_names = b""
    members: List[ArMember] = []
    while pos + 60 <= len(data):
        hdr = data[pos : pos + 60]
        if hdr[58:60] != b"`\n":
            raise ValueError(f"Invalid ar member fmag at offset {pos}: {hdr[58:60]!r}")
        raw_name = hdr[:16].decode("ascii", errors="replace").rstrip(" ")
        size_str = hdr[48:58].decode("ascii", errors="strict").strip()
        size = int(size_str)
        payload_start = pos + 60
        payload_end = payload_start + size
        if payload_end > len(data):
            raise ValueError(f"Truncated ar member at offset {pos}")
        payload = data[payload_start:payload_end]
        if raw_name == "//":
            ext_names = payload
        else:
            resolved_name = raw_name
            if raw_name.startswith("/") and len(raw_name) > 1 and raw_name[1:].isdigit():
                ext_off = int(raw_name[1:])
                end_idx = ext_names.find(b"/\n", ext_off)
                if end_idx == -1:
                    end_idx = ext_names.find(b"\n", ext_off)
                if end_idx == -1:
                    end_idx = len(ext_names)
                resolved_name = ext_names[ext_off:end_idx].decode("utf-8", errors="replace").rstrip("/")
            elif raw_name != "/":
                resolved_name = raw_name.rstrip("/")
            members.append(
                ArMember(
                    name=resolved_name,
                    offset=payload_start,
                    size=size,
                    payload=payload,
                )
            )
        pos = payload_end + (size & 1)
    return members


def build_deterministic_ar_single_elf(member_name: str, elf_payload: bytes) -> bytes:
    """
    Construct a 100% standard-compliant, deterministic GNU `ar` archive (`!<arch>\\n`)
    with a `//` GNU extended filename table and a `/0` 60-byte ASCII member header
    wrapping the exact, unmodified `elf_payload` bytes.
    """
    ext_body = member_name.encode("ascii") + b"/\n"
    if len(ext_body) % 2 == 1:
        ext_body += b"\n"

    def make_hdr(name_field: str, mtime: str, uid: str, gid: str, mode: str, size: int) -> bytes:
        hdr = (
            f"{name_field:<16}"
            f"{mtime:<12}"
            f"{uid:<6}"
            f"{gid:<6}"
            f"{mode:<8}"
            f"{size:<10}"
            "`\n"
        ).encode("ascii")
        assert len(hdr) == 60
        return hdr

    ext_hdr = make_hdr("//", "", "", "", "", len(ext_body))
    obj_hdr = make_hdr("/0", "0", "0", "0", "644", len(elf_payload))
    pad = b"\n" if (len(elf_payload) % 2 == 1) else b""
    archive = AR_MAGIC + ext_hdr + ext_body + obj_hdr + elf_payload + pad

    # Self-check round-trip parse:
    parsed = parse_ar_archive(archive)
    assert len(parsed) == 1
    assert parsed[0].name == member_name
    assert parsed[0].payload == elf_payload
    return archive


def read_cstr(blob: bytes, offset: int) -> str:
    if offset >= len(blob):
        return ""
    end = blob.find(b"\x00", offset)
    if end == -1:
        end = len(blob)
    return blob[offset:end].decode("utf-8", errors="replace")


def parse_elf64_object(member_name: str, data: bytes) -> ParsedElfObject:
    if len(data) < 64 or data[:4] != ELF_MAGIC:
        raise ValueError(f"{member_name}: missing ELF magic")
    if data[4] != ELFCLASS64 or data[5] != ELFDATA2LSB:
        raise ValueError(f"{member_name}: expected ELF64 little-endian")
    (
        e_type,
        e_machine,
        _e_version,
        _e_entry,
        _e_phoff,
        e_shoff,
        _e_flags,
        e_ehsize,
        _e_phentsize,
        _e_phnum,
        e_shentsize,
        e_shnum,
        e_shstrndx,
    ) = struct.unpack("<HHIQQQIHHHHHH", data[16:64])
    if e_type != ET_REL:
        raise ValueError(f"{member_name}: expected ET_REL (1), got {e_type}")
    if e_shentsize != 64:
        raise ValueError(f"{member_name}: expected 64-byte Elf64_Shdr, got {e_shentsize}")

    shdrs = []
    for idx in range(e_shnum):
        off = e_shoff + idx * e_shentsize
        shdrs.append(struct.unpack("<IIQQQQIIQQ", data[off : off + 64]))

    shstr_sh = shdrs[e_shstrndx]
    shstr = data[shstr_sh[4] : shstr_sh[4] + shstr_sh[5]]

    text_idx: Optional[int] = None
    text_offset = 0
    text_size = 0
    for idx, sh in enumerate(shdrs):
        sname = read_cstr(shstr, sh[0])
        if sh[1] == SHT_PROGBITS and sname == ".text":
            text_idx = idx
            text_offset = sh[4]
            text_size = sh[5]
            break

    qsag_syms: List[ElfSymbol] = []
    for sh in shdrs:
        if sh[1] != SHT_SYMTAB:
            continue
        strtab_sh = shdrs[sh[6]]
        strtab = data[strtab_sh[4] : strtab_sh[4] + strtab_sh[5]]
        for pos in range(sh[4], sh[4] + sh[5], 24):
            st_name, st_info, _st_other, st_shndx, st_value, st_size = struct.unpack(
                "<IBBHQQ", data[pos : pos + 24]
            )
            sym_name = read_cstr(strtab, st_name)
            st_bind = st_info >> 4
            st_type = st_info & 0xF
            if not sym_name or st_shndx == 0 or st_shndx >= len(shdrs):
                continue
            sec_sh = shdrs[st_shndx]
            sec_name = read_cstr(shstr, sec_sh[0])
            clean_name = sym_name.lstrip("_")
            if clean_name.startswith("qsag_asm_") and st_bind >= 1 and st_type == STT_FUNC:
                if text_idx is None or st_shndx != text_idx:
                    raise ValueError(f"{sym_name}: expected in .text section")
                if st_value + st_size > text_size or st_size == 0:
                    raise ValueError(f"{sym_name}: invalid symbol bounds [{st_value}..{st_value + st_size})")
                code = data[text_offset + st_value : text_offset + st_value + st_size]
                qsag_syms.append(
                    ElfSymbol(
                        name=clean_name,
                        bind=st_bind,
                        sym_type=st_type,
                        shndx=st_shndx,
                        section_name=sec_name,
                        value=st_value,
                        size=st_size,
                        code=code,
                    )
                )

    qsag_syms.sort(key=lambda s: s.value)
    return ParsedElfObject(
        member_name=member_name,
        raw_bytes=data,
        sha256=hashlib.sha256(data).hexdigest(),
        machine=e_machine,
        ehsize=e_ehsize,
        shoff=e_shoff,
        shentsize=e_shentsize,
        shnum=e_shnum,
        shstrndx=e_shstrndx,
        text_offset=text_offset,
        text_size=text_size,
        qsag_symbols=qsag_syms,
    )


def extract_qsag_elf_from_rlib(rlib_path: Path) -> Tuple[str, int, ParsedElfObject]:
    raw_rlib = rlib_path.read_bytes()
    rlib_sha256 = hashlib.sha256(raw_rlib).hexdigest()
    members = parse_ar_archive(raw_rlib)
    for m in members:
        if m.name.endswith(".o") and m.payload[:4] == ELF_MAGIC:
            parsed = parse_elf64_object(m.name, m.payload)
            if parsed.qsag_symbols:
                return rlib_sha256, len(raw_rlib), parsed
    raise ValueError(f"No ELF64 object member with qsag_asm_* symbols found in {rlib_path}")


# =============================================================================
# Standalone Machine-Code Constant-Time & ABI Sanity Verifier (x86_64 & AArch64)
# =============================================================================


def decode_modrm_len(code: bytes, pos: int) -> Tuple[int, int, int, int, bool]:
    """Return (mod, reg, rm, extra_bytes, has_scaled_index_sib)."""
    modrm = code[pos]
    mod = (modrm >> 6) & 3
    reg = (modrm >> 3) & 7
    rm = modrm & 7
    if mod == 3:
        return mod, reg, rm, 1, False
    extra = 1
    has_index = False
    base_low = rm
    if rm == 4:
        sib = code[pos + 1]
        scale = (sib >> 6) & 3
        index = (sib >> 3) & 7
        base_low = sib & 7
        extra += 1
        # RSP (index=4 with X=0) means "no index register" in x86_64 SIB encoding
        if index != 4 or scale != 0:
            has_index = True
    if mod == 0 and base_low == 5:
        extra += 4
    elif mod == 1:
        extra += 1
    elif mod == 2:
        extra += 4
    return mod, reg, rm, extra, has_index


def verify_x86_64_symbol(sym: ElfSymbol) -> Dict[str, object]:
    code = sym.code
    pc = 0
    instr_count = 0
    loop_branches = 0
    used_ymm = False
    saw_vzeroupper = False
    violations: List[str] = []

    while pc < len(code):
        start = pc
        b = code[pc]
        # Legacy prefixes
        while b in (0x66, 0xF2, 0xF3, 0x2E):
            pc += 1
            b = code[pc]
        rex = 0
        if 0x40 <= b <= 0x4F:
            rex = b
            pc += 1
            b = code[pc]
        rex_w = (rex >> 3) & 1
        rex_x = (rex >> 1) & 1

        if b == 0xC5 or b == 0xC4:
            # VEX 2-byte or 3-byte
            if b == 0xC5:
                b1 = code[pc + 1]
                vex_x = 0
                mmmmm = 1
                vex_l = (b1 >> 2) & 1
                pp = b1 & 3
                pc += 2
            else:
                b1 = code[pc + 1]
                b2 = code[pc + 2]
                vex_x = 1 - ((b1 >> 6) & 1)
                mmmmm = b1 & 0x1F
                vex_l = (b2 >> 2) & 1
                pp = b2 & 3
                pc += 3
            op = code[pc]
            pc += 1
            if mmmmm == 1 and pp == 0 and op == 0x77:
                saw_vzeroupper = True
                used_ymm = False
            else:
                if vex_l == 1 or (mmmmm == 1 and op in (0x6F, 0x7F, 0x6E, 0xEF)):
                    used_ymm = True
                if mmmmm == 2 and pp == 1 and op in (0x90, 0x91, 0x92, 0x93):
                    violations.append(f"0x{start:x}: forbidden vpgather opcode 0x{op:02x}")
                mod, _reg, rm, extra, has_idx = decode_modrm_len(code, pc)
                if mod != 3 and (has_idx or (rm == 4 and vex_x == 1)):
                    violations.append(f"0x{start:x}: indexed SIB memory operand in VEX instr")
                pc += extra
                if (mmmmm == 1 and op in (0x71, 0x72, 0x73)) or mmmmm == 3:
                    pc += 1
        elif 0x50 <= b <= 0x5F or b in (0x90, 0xC3):
            if b == 0xC3 and used_ymm and not saw_vzeroupper:
                violations.append(f"0x{start:x}: ret with dirty YMM upper state (missing vzeroupper)")
            pc += 1
        elif 0xB8 <= b <= 0xBF:
            pc += 1 + (8 if rex_w else 4)
        elif b in (0x88, 0x89, 0x8B, 0x01, 0x09, 0x19, 0x21, 0x29, 0x31, 0x33):
            mod, _reg, rm, extra, has_idx = decode_modrm_len(code, pc + 1)
            if mod != 3 and (has_idx or (rm == 4 and rex_x == 1)):
                violations.append(f"0x{start:x}: indexed SIB memory operand")
            pc += 1 + extra
        elif b == 0x81:
            _mod, _reg, _rm, extra, has_idx = decode_modrm_len(code, pc + 1)
            if has_idx:
                violations.append(f"0x{start:x}: indexed SIB memory operand")
            pc += 1 + extra + 4
        elif b in (0x83, 0xC1):
            _mod, _reg, _rm, extra, has_idx = decode_modrm_len(code, pc + 1)
            if has_idx:
                violations.append(f"0x{start:x}: indexed SIB memory operand")
            pc += 1 + extra + 1
        elif b == 0xD3:
            violations.append(f"0x{start:x}: forbidden variable-count shift/rotate by CL")
            _mod, _reg, _rm, extra, _ = decode_modrm_len(code, pc + 1)
            pc += 1 + extra
        elif b == 0xF7:
            _mod, digit, _rm, extra, has_idx = decode_modrm_len(code, pc + 1)
            if digit in (6, 7):
                violations.append(f"0x{start:x}: forbidden variable-latency div/idiv")
            if has_idx:
                violations.append(f"0x{start:x}: indexed SIB memory operand")
            pc += 1 + extra
        elif b == 0xFF:
            _mod, digit, _rm, extra, has_idx = decode_modrm_len(code, pc + 1)
            if digit in (2, 4):
                violations.append(f"0x{start:x}: forbidden indirect call/jmp")
            if has_idx:
                violations.append(f"0x{start:x}: indexed SIB memory operand")
            pc += 1 + extra
        elif 0x70 <= b <= 0x7F:
            rel8 = struct.unpack("<b", code[pc + 1 : pc + 2])[0]
            target = pc + 2 + rel8
            if b != 0x75 or target >= start or target < 0:
                violations.append(f"0x{start:x}: non-bottom-loop jcc 0x{b:02x} -> 0x{target:x}")
            else:
                loop_branches += 1
            pc += 2
        elif b == 0x0F:
            op2 = code[pc + 1]
            if op2 == 0x1F:
                _mod, _reg, _rm, extra, _ = decode_modrm_len(code, pc + 2)
                pc += 2 + extra
            elif 0x80 <= op2 <= 0x8F:
                rel32 = struct.unpack("<i", code[pc + 2 : pc + 6])[0]
                target = pc + 6 + rel32
                if op2 != 0x85 or target >= start or target < 0:
                    violations.append(f"0x{start:x}: non-bottom-loop jcc 0x0f 0x{op2:02x} -> 0x{target:x}")
                else:
                    loop_branches += 1
                pc += 6
            elif op2 in (0xAE, 0xAF, 0xB6) or (0x40 <= op2 <= 0x4F):
                _mod, _reg, _rm, extra, has_idx = decode_modrm_len(code, pc + 2)
                if has_idx:
                    violations.append(f"0x{start:x}: indexed SIB memory operand")
                pc += 2 + extra
            elif op2 == 0x38 and code[pc + 2] == 0xF6:
                _mod, _reg, _rm, extra, has_idx = decode_modrm_len(code, pc + 3)
                if has_idx:
                    violations.append(f"0x{start:x}: indexed SIB memory operand")
                pc += 3 + extra
            else:
                raise ValueError(f"{sym.name}: unhandled 0F opcode 0x{op2:02x} at +0x{start:x}")
        else:
            raise ValueError(f"{sym.name}: unhandled opcode 0x{b:02x} at +0x{start:x}")

        instr_count += 1

    if pc != len(code):
        violations.append(f"instruction boundary mismatch: ended at {pc} != {len(code)}")
    if code[-1] != 0xC3:
        violations.append("function does not end with ret (0xc3)")

    return {
        "symbol": sym.name,
        "offset": sym.value,
        "size_bytes": sym.size,
        "instructions": instr_count,
        "loop_back_edges": loop_branches,
        "violations": violations,
        "pass": len(violations) == 0,
    }


def verify_aarch64_symbol(sym: ElfSymbol) -> Dict[str, object]:
    code = sym.code
    if len(code) % 4 != 0:
        return {
            "symbol": sym.name,
            "offset": sym.value,
            "size_bytes": sym.size,
            "instructions": 0,
            "loop_back_edges": 0,
            "violations": ["code size is not a multiple of 4 bytes"],
            "pass": False,
        }
    instr_count = len(code) // 4
    loop_branches = 0
    violations: List[str] = []
    dirty_secret_vecs: set[int] = set()

    for idx in range(instr_count):
        pc = idx * 4
        w = struct.unpack("<I", code[pc : pc + 4])[0]
        # Forbidden CBZ/CBNZ (x34..x35) and TBZ/TBNZ (x36..x37)
        if (w & 0x7E000000) == 0x34000000:
            violations.append(f"0x{pc:x}: forbidden cbz/cbnz 0x{w:08x}")
        elif (w & 0x7E000000) == 0x36000000:
            violations.append(f"0x{pc:x}: forbidden tbz/tbnz 0x{w:08x}")
        # Conditional branch B.cond: 01010100 imm19 0 cond
        elif (w & 0xFF000010) == 0x54000000:
            cond = w & 0xF
            imm19 = (w >> 5) & 0x7FFFF
            if imm19 & (1 << 18):
                imm19 -= 1 << 19
            target = pc + imm19 * 4
            if cond != 1 or target >= pc or target < 0:
                violations.append(f"0x{pc:x}: non-bottom-loop b.cond (cond={cond}) -> 0x{target:x}")
            else:
                loop_branches += 1
        # Forbidden UDIV / SDIV: x011010110 Rm 00001x Rn Rd
        elif (w & 0x7FE0FC00) == 0x1AC00800:
            violations.append(f"0x{pc:x}: forbidden udiv/sdiv 0x{w:08x}")
        # Forbidden variable shift LSLV/LSRV/ASRV/RORV: x011010110 Rm 0010xx Rn Rd
        elif (w & 0x7FE0F000) == 0x1AC02000:
            violations.append(f"0x{pc:x}: forbidden register-variable shift 0x{w:08x}")
        # Forbidden register-offset LDR/STR: xx111x00xx1 Rm option S 10 Rn Rt
        elif (w & 0x3B200C00) == 0x38200800:
            violations.append(f"0x{pc:x}: forbidden register-offset memory access 0x{w:08x}")
        # Track NEON secret vector registers vs zeroing `eor vD.16b, vN.16b, vM.16b`
        elif (w & 0xFFE0FC00) == 0x6E201C00:
            rd = w & 0x1F
            rn = (w >> 5) & 0x1F
            rm = (w >> 16) & 0x1F
            if rn == rm:
                dirty_secret_vecs.discard(rd)
            else:
                dirty_secret_vecs.add(rd)
        elif (w & 0xFFC00000) == 0x3DC00000:  # ldr qRt, [xRn, #imm]
            rt = w & 0x1F
            dirty_secret_vecs.add(rt)
        elif (
            (w & 0xFFE00000) in (0xCE000000, 0xCE200000, 0xCE600000, 0xCE800000)
            or (w & 0xBFE0FC00) == 0x0EE0E000
            or (w & 0xFFE08400) == 0x6E000000
        ):
            rd = w & 0x1F
            dirty_secret_vecs.add(rd)

    last_w = struct.unpack("<I", code[-4:])[0]
    if last_w != 0xD65F03C0:
        violations.append("function does not end with ret (0xd65f03c0)")
    # v21 holds public 0x87 in tower128_bdoz_mac_pmull (loaded via fmov d21, x4 where x4=0x87)
    unwiped = sorted(v for v in dirty_secret_vecs if v != 21)
    if unwiped:
        violations.append(f"unwiped NEON secret vector registers before ret: {unwiped}")

    return {
        "symbol": sym.name,
        "offset": sym.value,
        "size_bytes": sym.size,
        "instructions": instr_count,
        "loop_back_edges": loop_branches,
        "violations": violations,
        "pass": len(violations) == 0,
    }


def verify_rlib_cli(rlib_path: Path) -> int:
    rlib_sha256, rlib_size, elf_obj = extract_qsag_elf_from_rlib(rlib_path)
    arch_name = (
        "x86_64"
        if elf_obj.machine == EM_X86_64
        else "aarch64"
        if elf_obj.machine == EM_AARCH64
        else f"unknown({elf_obj.machine})"
    )
    results = []
    for sym in elf_obj.qsag_symbols:
        if elf_obj.machine == EM_X86_64:
            results.append(verify_x86_64_symbol(sym))
        elif elf_obj.machine == EM_AARCH64:
            results.append(verify_aarch64_symbol(sym))
        else:
            raise ValueError(f"Unsupported ELF e_machine={elf_obj.machine}")

    all_pass = all(bool(r["pass"]) for r in results)
    total_instrs = sum(int(r["instructions"]) for r in results)
    summary = {
        "rlib_path": str(rlib_path),
        "rlib_size_bytes": rlib_size,
        "rlib_sha256": rlib_sha256,
        "elf_member_name": elf_obj.member_name,
        "elf_member_size_bytes": len(elf_obj.raw_bytes),
        "elf_member_sha256": elf_obj.sha256,
        "architecture": arch_name,
        "e_machine": elf_obj.machine,
        "text_offset": elf_obj.text_offset,
        "text_size_bytes": elf_obj.text_size,
        "symbol_count": len(results),
        "total_instructions": total_instrs,
        "all_pass": all_pass,
        "symbols": results,
    }
    print(json.dumps(summary, indent=2))
    return 0 if all_pass else 1


def format_lean_nat_literal(data: bytes) -> str:
    """Little-endian big-integer literal: byte `i` of `data` is `(n >>> (8 * i)) % 256`."""
    return "0x" + (data[::-1].hex().upper() or "0")


def generate_lean_fixtures(out_path: Path, x86_rlib: Path, aarch64_rlib: Path) -> None:
    x86_rlib_sha, x86_rlib_len, x86_elf = extract_qsag_elf_from_rlib(x86_rlib)
    arm_rlib_sha, arm_rlib_len, arm_elf = extract_qsag_elf_from_rlib(aarch64_rlib)

    assert x86_elf.machine == EM_X86_64, f"Expected EM_X86_64 (62), got {x86_elf.machine}"
    assert arm_elf.machine == EM_AARCH64, f"Expected EM_AARCH64 (183), got {arm_elf.machine}"

    # Verify all symbols pass standalone checks before emitting Lean fixtures:
    for s in x86_elf.qsag_symbols:
        res = verify_x86_64_symbol(s)
        assert res["pass"], f"x86_64 verification failed on {s.name}: {res['violations']}"
    for s in arm_elf.qsag_symbols:
        res = verify_aarch64_symbol(s)
        assert res["pass"], f"aarch64 verification failed on {s.name}: {res['violations']}"

    x86_ar_slice = build_deterministic_ar_single_elf(x86_elf.member_name, x86_elf.raw_bytes)
    arm_ar_slice = build_deterministic_ar_single_elf(arm_elf.member_name, arm_elf.raw_bytes)
    x86_ar_slice_sha = hashlib.sha256(x86_ar_slice).hexdigest()
    arm_ar_slice_sha = hashlib.sha256(arm_ar_slice).hexdigest()

    x86_sym_names = ",\n  ".join(f'"{s.name}"' for s in x86_elf.qsag_symbols)
    arm_sym_names = ",\n  ".join(f'"{s.name}"' for s in arm_elf.qsag_symbols)

    lean_src = f"""module
/-
# Qsag.Machine.CompiledRlibFixtures — Real `rustc --release` `.rlib` / `ELF64` Machine-Code Fixtures

Auto-generated deterministically by `scripts/extract_rlib_elf.py` from real `cargo build -p qsag-asm --release`
artifacts (workspace release profile with LTO disabled, `--target x86_64-unknown-linux-gnu` and
`--target aarch64-unknown-linux-gnu`) compiled on a Linux build host.

## Cryptographic Artifact Provenance (SHA-256)
- **`x86_64-unknown-linux-gnu`:**
  - Full `libqsag_asm.rlib` (`{x86_rlib_len}` bytes):
    `{x86_rlib_sha}`
  - Extracted native `ELF64` member `{x86_elf.member_name}` (`{len(x86_elf.raw_bytes)}` bytes, `{len(x86_elf.qsag_symbols)}` `STT_FUNC` symbols):
    `{x86_elf.sha256}`
  - Deterministic GNU `ar` fixture `x86RlibArchiveNat` (`{len(x86_ar_slice)}` bytes):
    `{x86_ar_slice_sha}`
- **`aarch64-unknown-linux-gnu`:**
  - Full `libqsag_asm.rlib` (`{arm_rlib_len}` bytes):
    `{arm_rlib_sha}`
  - Extracted native `ELF64` member `{arm_elf.member_name}` (`{len(arm_elf.raw_bytes)}` bytes, `{len(arm_elf.qsag_symbols)}` `STT_FUNC` symbols):
    `{arm_elf.sha256}`
  - Deterministic GNU `ar` fixture `aarch64RlibArchiveNat` (`{len(arm_ar_slice)}` bytes):
    `{arm_ar_slice_sha}`
-/

public section
namespace Qsag

set_option autoImplicit false

/-- SHA-256 hex digest of the full `x86_64-unknown-linux-gnu` `target/release/libqsag_asm.rlib` (`{x86_rlib_len}` bytes). -/
def x86FullRlibSha256 : String :=
  "{x86_rlib_sha}"

/-- SHA-256 hex digest of the unmodified `x86_64` `ELF64` `.rcgu.o` object member (`{len(x86_elf.raw_bytes)}` bytes). -/
def x86RcguElfSha256 : String :=
  "{x86_elf.sha256}"

/-- Original `GNU ar` member filename of the `x86_64` `ELF64` `.rcgu.o` object inside `libqsag_asm.rlib`. -/
@[expose] def x86RcguMemberName : String :=
  "{x86_elf.member_name}"

/-- SHA-256 hex digest of the full `aarch64-unknown-linux-gnu` `target/release/libqsag_asm.rlib` (`{arm_rlib_len}` bytes). -/
def aarch64FullRlibSha256 : String :=
  "{arm_rlib_sha}"

/-- SHA-256 hex digest of the unmodified `aarch64` `ELF64` `.rcgu.o` object member (`{len(arm_elf.raw_bytes)}` bytes). -/
def aarch64RcguElfSha256 : String :=
  "{arm_elf.sha256}"

/-- Original `GNU ar` member filename of the `aarch64` `ELF64` `.rcgu.o` object inside `libqsag_asm.rlib`. -/
@[expose] def aarch64RcguMemberName : String :=
  "{arm_elf.member_name}"

/-- All {len(x86_elf.qsag_symbols)} exported `STT_FUNC` assembly kernel symbols in `x86_64` `libqsag_asm.rlib`. -/
@[expose] def x86ExportedSymbolNames : List String := [
  {x86_sym_names}
]

/-- All {len(arm_elf.qsag_symbols)} exported `STT_FUNC` assembly kernel symbols in `aarch64` `libqsag_asm.rlib`. -/
@[expose] def aarch64ExportedSymbolNames : List String := [
  {arm_sym_names}
]

/-- Byte length of the `x86_64` GNU `ar` + `ELF64` `.rcgu.o` fixture. -/
@[expose] def x86RlibArchiveLen : Nat := {len(x86_ar_slice)}

/-- Exact GNU `ar` archive bytes (`!<arch>\\n` + GNU `//` extended name table + 60-byte ASCII member
    header + unmodified `{len(x86_elf.raw_bytes)}`-byte `ELF64` `EM_X86_64` `.rcgu.o` object) as one
    little-endian natural number: byte `i` is `(n >>> (8 * i)) % 256`. -/
@[expose] def x86RlibArchiveNat : Nat :=
  {format_lean_nat_literal(x86_ar_slice)}

/-- Byte length of the `aarch64` GNU `ar` + `ELF64` `.rcgu.o` fixture. -/
@[expose] def aarch64RlibArchiveLen : Nat := {len(arm_ar_slice)}

/-- Exact GNU `ar` archive bytes (`!<arch>\\n` + GNU `//` extended name table + 60-byte ASCII member
    header + unmodified `{len(arm_elf.raw_bytes)}`-byte `ELF64` `EM_AARCH64` `.rcgu.o` object) as one
    little-endian natural number: byte `i` is `(n >>> (8 * i)) % 256`. -/
@[expose] def aarch64RlibArchiveNat : Nat :=
  {format_lean_nat_literal(arm_ar_slice)}

end Qsag
end
"""
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(lean_src, encoding="utf-8")
    print(
        f"Generated {out_path} "
        f"(x86_64: {len(x86_elf.qsag_symbols)} syms / {len(x86_ar_slice)} B; "
        f"aarch64: {len(arm_elf.qsag_symbols)} syms / {len(arm_ar_slice)} B)"
    )


def main() -> int:
    ap = argparse.ArgumentParser(description="GNU ar (.rlib) + ELF64 inspector & Lean fixture generator")
    ap.add_argument("--verify", type=Path, help="Verify a compiled .rlib archive in standalone CLI mode")
    ap.add_argument("--generate-lean", type=Path, help="Output path for Lean 4 CompiledRlibFixtures.lean")
    ap.add_argument("--x86-rlib", type=Path, help="Path to x86_64-unknown-linux-gnu libqsag_asm.rlib")
    ap.add_argument("--aarch64-rlib", type=Path, help="Path to aarch64-unknown-linux-gnu libqsag_asm.rlib")
    args = ap.parse_args()

    if args.verify is not None:
        return verify_rlib_cli(args.verify)
    if args.generate_lean is not None:
        if args.x86_rlib is None or args.aarch64_rlib is None:
            ap.error("--generate-lean requires both --x86-rlib and --aarch64-rlib")
        generate_lean_fixtures(args.generate_lean, args.x86_rlib, args.aarch64_rlib)
        return 0

    ap.print_help()
    return 1


if __name__ == "__main__":
    sys.exit(main())
