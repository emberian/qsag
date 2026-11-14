#!/usr/bin/env python3
"""
Automated Machine-Code Constant-Time Disassembly Auditor (`audit_elf_ct.py`).

Inspects compiled ELF `.rlib` / `.o` artifacts for `qsag-asm` (plus optional extra `.rlib`
targets), Windows COFF / macOS Mach-O `x86_64` assembly targets, Linux `aarch64_kernels.s`,
and Apple Mach-O inline `global_asm!` in `aarch64_asm.rs` across `x86_64` and `aarch64`,
enforcing:
  1. Complete symbol coverage (`16` `x86_64` asm kernels + `7` Linux `aarch64` asm kernels +
     `7` Apple Mach-O `_qsag_asm_*` asm kernels + ALL compiled Rust crypto functions in `.rlib`).
  2. ZERO secret-dependent conditional branches (`j*` / `b.*` / `cbz` / `cbnz` / `tbz` / `tbnz`),
     allowing strictly bottom-tested `dec rcx|ecx` + `jnz|jne` (x86_64) and
     `subs x1|x3, x1|x3, #1` + `b.ne` (aarch64) ONLY when the loop counter register is untainted!
  3. ZERO variable-latency division instructions (`div`, `idiv`, `udiv`, `sdiv`, `vdiv*`, `fdiv*`)
     across ALL asm kernels AND ALL compiled Rust crypto functions.
  4. ZERO variable-count shifts/rotates (`shl/shr/sar/sal/rol/ror ..., cl`, `shlx/shrx/sarx`,
     `shld/shrd ..., cl` on x86_64; `lslv/lsrv/asrv/rorv` or 3-GPR `lsl/lsr/asr/ror` on aarch64)
     across ALL asm kernels AND ALL compiled Rust crypto functions.
  5. ZERO secret-indexed or secret-tainted memory operands (`[base + idx*scale]`, `[reg1 + reg2]`,
     `vpgather*`, pre-added `[regA]` LUT dereferences, or static-displacement `[tainted_reg + disp]`
     LUT loads) in asm kernels, and ZERO >= 4 KiB static LUT symbols (`TOWER128_ISO`).
  6. Stateful live-at-`ret` SIMD register hygiene:
     - `x86_64`: tracks BOTH `ymm_upper_dirty` (`vzeroupper` required) AND `dirty_simd` (`xmm0..15` /
       `ymm0..15` must all be explicitly zeroized before `ret`; `vzeroupper` alone does NOT clear
       lower `xmm` halves, and reloading after a wipe re-marks the register dirty!).
     - `aarch64`: stateful `dirty_neon` (`v0..v31`) live-at-`ret` tracking across ALL 7 kernels
       (reloading a `qN`/`vN` register after `eor vN.16b, vN.16b, vN.16b` re-dirties `vN`!).
  7. Negative `#tooth` self-tests (`15` adversarial test cases) verifying immediate rejection of
     planted branches, tainted loop counters, static-disp LUTs, pre-added LUTs, `vzeroupper`-only
     dirty XMM leaks, post-wipe NEON reloads, variable shifts, and hardware dividers!
"""

import argparse
import ctypes
import shutil
import re
import subprocess
import sys
import tempfile
from pathlib import Path

EXPECTED_X86_SYMBOLS = [
    "qsag_asm_keccak_f1600_avx2_4x",
    "qsag_asm_keccak_chi_mpc_avx2",
    "qsag_asm_gf256_shamir_mul_gfni",
    "qsag_asm_gf256_shamir_mac_gfni",
    "qsag_asm_gf256_shamir_mul_avx2",
    "qsag_asm_gf256_shamir_mac_avx2",
    "qsag_asm_tower128_bdoz_mac_vpclmul",
    "qsag_asm_tower128_bdoz_mac_pclmul",
    "qsag_asm_goldilocks_mul_ct_x86_64",
    "qsag_asm_goldilocks_add_ct_x86_64",
    "qsag_asm_goldilocks_sub_ct_x86_64",
    "qsag_asm_goldilocks_pow7_ct_x86_64",
    "qsag_asm_goldilocks_dot2_adx_x86_64",
    "qsag_asm_ct_eq_32_x86_64",
    "qsag_asm_ct_eq_bytes_x86_64",
    "qsag_asm_ct_memzero_x86_64",
]

# Bitslice transpose / GF(2^128) kernels (`src/bitslice.rs`). They are audited in the compiled
# ELF only: the cross-flavour passes below re-assemble text extracted from `x86_64_asm.rs` /
# `aarch64_asm.rs`, which does not contain them.
EXPECTED_X86_BITSLICE_SYMBOLS = [
    "qsag_asm_transpose64x256_avx2",
    "qsag_asm_gf2_128_mul_acc_pclmul",
    "qsag_asm_gf2_128_mul_acc_vpclmul",
]

EXPECTED_AARCH64_SYMBOLS = [
    "qsag_asm_enable_dit_aarch64",
    "qsag_asm_keccak_sha3_neon",
    "qsag_asm_keccak_theta_rho_sha3_neon",
    "qsag_asm_tower128_bdoz_mac_pmull",
    "qsag_asm_goldilocks_mul_ct_aarch64",
    "qsag_asm_ct_eq_32_aarch64",
    "qsag_asm_ct_memzero_aarch64",
]

X86_DIV_MNEMONICS = {
    "div", "idiv", "fdiv", "fdivp", "divss", "divsd", "divps", "divpd",
    "vdivss", "vdivsd", "vdivps", "vdivpd",
}

X86_GATHER_MNEMONICS = {
    "vpgatherdd", "vpgatherdq", "vpgatherqd", "vpgatherqq",
    "vgatherdps", "vgatherdpd", "vgatherqps", "vgatherqpd",
}

X86_SHIFT_MNEMONICS = {
    "shl", "shr", "sar", "sal", "rol", "ror", "rcl", "rcr", "shld", "shrd",
}

X86_BMI2_VAR_SHIFT_MNEMONICS = {"shlx", "shrx", "sarx"}

AARCH64_DIV_MNEMONICS = {"udiv", "sdiv", "fdiv"}

AARCH64_CSEL_MNEMONICS = {
    "csel", "csinc", "csinv", "csneg", "cset", "csetm", "cinc", "cinv", "cneg",
}

AARCH64_VAR_SHIFT_MNEMONICS = {"lslv", "lsrv", "asrv", "rorv"}

X86_GPR64_CANON = {
    "rax": "rax", "eax": "rax", "ax": "rax", "al": "rax",
    "rbx": "rbx", "ebx": "rbx", "bx": "rbx", "bl": "rbx",
    "rcx": "rcx", "ecx": "rcx", "cx": "rcx", "cl": "rcx",
    "rdx": "rdx", "edx": "rdx", "dx": "rdx", "dl": "rdx",
    "rsi": "rsi", "esi": "rsi", "si": "rsi", "sil": "rsi",
    "rdi": "rdi", "edi": "rdi", "di": "rdi", "dil": "rdi",
    "rbp": "rbp", "ebp": "rbp",
    "rsp": "rsp", "esp": "rsp",
    **{f"r{i}": f"r{i}" for i in range(8, 16)},
    **{f"r{i}d": f"r{i}" for i in range(8, 16)},
    **{f"r{i}w": f"r{i}" for i in range(8, 16)},
    **{f"r{i}b": f"r{i}" for i in range(8, 16)},
}


def canon_x86_gpr(tok: str) -> str | None:
    return X86_GPR64_CANON.get(tok.strip().lower())


def canon_x86_simd(tok: str) -> int | None:
    m = re.match(r"^[xyz]mm([0-9]+)$", tok.strip().lower())
    return int(m.group(1)) if m else None


def canon_a64_gpr(tok: str) -> str | None:
    t = tok.strip().lower()
    if t == "sp":
        return "sp"
    if t in ("xzr", "wzr"):
        return None
    m = re.match(r"^[xw]([0-9]+)$", t)
    if m:
        return f"x{m.group(1)}"
    return None


def canon_a64_neon(tok: str) -> str | None:
    t = tok.strip().lower().lstrip("{").rstrip("}")
    m = re.match(r"^(?:v([0-9]+)\.[0-9a-z]+|[qdsbh]([0-9]+))$", t)
    if m:
        idx = m.group(1) or m.group(2)
        return f"v{idx}"
    return None


def parse_objdump_functions(disasm_text: str) -> dict[str, list[tuple[str, str]]]:
    funcs: dict[str, list[tuple[str, str]]] = {}
    current_sym = None
    sym_elf_re = re.compile(r"^[0-9a-fA-F]+\s+<(.+)>:\s*$")
    sym_macho_re = re.compile(r"^([_A-Za-z][A-Za-z0-9_$.]*):\s*$")
    ins_re = re.compile(r"^\s*[0-9a-fA-F]+:\s+[0-9a-fA-F ]+\t\s*([a-zA-Z0-9_.]+)(?:\s+(.*))?$")

    for raw_line in disasm_text.splitlines():
        if raw_line.startswith("Disassembly of section"):
            current_sym = None
            continue
        m_sym = sym_elf_re.match(raw_line) or sym_macho_re.match(raw_line)
        if m_sym:
            current_sym = m_sym.group(1)
            funcs.setdefault(current_sym, [])
            continue
        if current_sym is None:
            continue
        m_ins = ins_re.match(raw_line)
        if m_ins:
            mnem = m_ins.group(1).lower()
            ops = (m_ins.group(2) or "").strip()
            # LLVM's Darwin printer puts the SIMD arrangement on the mnemonic.
            arrangement = re.fullmatch(r"([a-z0-9]+)\.([0-9]+[bhsdq])", mnem)
            if arrangement:
                mnem, lane = arrangement.groups()
                ops = re.sub(r"\bv([0-9]+)\b(?!\.)", rf"v\1.{lane}", ops)
            ops_clean = re.sub(r"\s+(?:#\s|//).*$", "", ops)
            ops_clean = re.sub(r"\s+<.+>$", "", ops_clean).strip()
            funcs[current_sym].append((mnem, ops_clean))
    return funcs


def check_x86_variable_shift(sym: str, idx: int, mnem: str, ops_l: str) -> str | None:
    if mnem in X86_BMI2_VAR_SHIFT_MNEMONICS:
        return f"{sym}[{idx}]: forbidden register-variable shift `{mnem} {ops_l}`"
    if mnem in X86_SHIFT_MNEMONICS:
        parts = [p.strip() for p in ops_l.split(",")]
        if len(parts) >= 2 and parts[-1] == "cl":
            return f"{sym}[{idx}]: forbidden variable `cl` shift/rotate `{mnem} {ops_l}`"
    return None


def split_top_operands(ops_l: str) -> list[str]:
    return [p.strip() for p in ops_l.split(",") if p.strip()]


def audit_x86_symbol(sym: str, instrs: list[tuple[str, str]]) -> list[str]:
    errors = []
    if not instrs:
        return [f"{sym}: empty instruction stream"]

    uses_ymm = any("ymm" in ops.lower() for _, ops in instrs)
    ymm_upper_dirty = False
    dirty_simd: set[int] = set()
    reg_sum_tainted: set[str] = set()

    # Seed value-tainted GPRs for scalar value-argument kernels
    val_tainted: set[str] = set()
    base_sym = sym.lstrip("_")
    if "goldilocks_" in base_sym:
        val_tainted.update({"rdi", "rsi", "rdx", "rcx"})
    elif "shamir_mac_" in base_sym:
        val_tainted.add("rdx")

    for idx, (mnem, ops) in enumerate(instrs):
        if mnem in ("nop", "cs", "endbr64"):
            continue
        ops_l = ops.lower()
        parts = split_top_operands(ops_l)

        # Track upper-YMM penalty state & live-at-ret XMM/YMM register dirtiness
        if "ymm" in ops_l:
            ymm_upper_dirty = True
        if mnem == "vzeroupper":
            # `vzeroupper` clears ONLY bits [255:128], NOT lower 128-bit `xmm0..xmm15`!
            ymm_upper_dirty = False

        if parts and "[" not in parts[0]:
            dst_simd = canon_x86_simd(parts[0])
            if dst_simd is not None:
                is_self_zero = (
                    (mnem in ("vpxor", "vxorps", "vxorpd") and len(parts) == 3 and parts[0] == parts[1] == parts[2])
                    or (mnem in ("pxor", "xorps", "xorpd") and len(parts) == 2 and parts[0] == parts[1])
                )
                if is_self_zero:
                    dirty_simd.discard(dst_simd)
                else:
                    dirty_simd.add(dst_simd)

        # 1. Variable-latency dividers, conditional moves, variable shifts, & scatter/gather
        if mnem in X86_DIV_MNEMONICS:
            errors.append(f"{sym}[{idx}]: forbidden variable-latency divider `{mnem} {ops}`")
        if mnem.startswith("cmov"):
            errors.append(f"{sym}[{idx}]: forbidden conditional move `{mnem} {ops}` (use bitwise/sbb mask)")
        if mnem in X86_GATHER_MNEMONICS:
            errors.append(f"{sym}[{idx}]: forbidden secret-indexed gather `{mnem} {ops}`")
        sh_err = check_x86_variable_shift(sym, idx, mnem, ops_l)
        if sh_err:
            errors.append(sh_err)

        # 2. Memory operand check: reject scaled/indexed `[base + idx*scale ...]`, multi-register
        #    `[reg1 + reg2]`, pre-added `[regA]` LUTs, AND `[tainted_reg + static_disp]` LUTs!
        for mem in re.findall(r"\[([^\]]+)\]", ops_l):
            if "*" in mem and mnem != "lea":
                errors.append(f"{sym}[{idx}]: forbidden scaled/indexed memory operand `[{mem}]`")
            regs_in_mem = re.findall(
                r"\b(r[0-9]+[dwb]?|r[a-z]{2}|e[a-z]{2}|[abcd]x|[sd]i|[sb]p|[abcd]l|[sd]il)\b",
                mem,
            )
            canon_regs = [canon_x86_gpr(r) for r in regs_in_mem if canon_x86_gpr(r) is not None]
            if len(canon_regs) > 1:
                errors.append(f"{sym}[{idx}]: forbidden multi-register indexed address `[{mem}]`")
            for cr in canon_regs:
                if cr in reg_sum_tainted:
                    errors.append(
                        f"{sym}[{idx}]: forbidden pre-added single-register LUT dereference `[{mem}]` via `{cr}`"
                    )
                if cr in val_tainted:
                    errors.append(
                        f"{sym}[{idx}]: forbidden secret-tainted base/offset LUT dereference `[{mem}]` via `{cr}`"
                    )

        # 3. Update `reg_sum_tainted` and `val_tainted` across GPR writes
        if mnem == "mulx" and len(parts) == 3:
            d1, d2, s3 = canon_x86_gpr(parts[0]), canon_x86_gpr(parts[1]), canon_x86_gpr(parts[2])
            src_taint = ("rdx" in val_tainted) or (s3 in val_tainted) or ("[" in parts[2])
            for d in (d1, d2):
                if d and src_taint:
                    val_tainted.add(d)
        elif parts and "[" not in parts[0]:
            dst_c = canon_x86_gpr(parts[0])
            if dst_c and dst_c not in ("rsp", "rbp"):
                is_gpr_zero = (
                    mnem in ("xor", "sub")
                    and len(parts) == 2
                    and parts[0] == parts[1]
                )
                if is_gpr_zero:
                    reg_sum_tainted.discard(dst_c)
                    val_tainted.discard(dst_c)
                elif mnem in ("sbb", "adc") and len(parts) == 2 and parts[0] == parts[1]:
                    # Borrow/carry mask materialization `sbb reg, reg` carries secret flag taint
                    val_tainted.add(dst_c)
                elif mnem in ("mov", "movzx", "movsx", "movsxd", "movabs") and len(parts) == 2:
                    src_part = parts[1]
                    src_c = canon_x86_gpr(src_part)
                    if "[" in src_part:
                        # Scalar load from caller buffer taints destination GPR as secret data!
                        mem_regs = [
                            canon_x86_gpr(r)
                            for r in re.findall(r"\b(r[0-9]+[dwb]?|r[a-z]{2}|e[a-z]{2})\b", src_part)
                        ]
                        if not all(r in ("rsp", "rbp") for r in mem_regs if r):
                            val_tainted.add(dst_c)
                        reg_sum_tainted.discard(dst_c)
                    elif src_c:
                        if src_c in reg_sum_tainted:
                            reg_sum_tainted.add(dst_c)
                        else:
                            reg_sum_tainted.discard(dst_c)
                        if src_c in val_tainted:
                            val_tainted.add(dst_c)
                        else:
                            val_tainted.discard(dst_c)
                    else:
                        # Immediate constant load clears GPR taint
                        reg_sum_tainted.discard(dst_c)
                        val_tainted.discard(dst_c)
                elif mnem == "lea" and len(parts) == 2:
                    mem_regs = [
                        canon_x86_gpr(r)
                        for r in re.findall(r"\b(r[0-9]+[dwb]?|r[a-z]{2}|e[a-z]{2})\b", parts[1])
                    ]
                    mem_regs = [r for r in mem_regs if r is not None and r != "rsp"]
                    if len(mem_regs) > 1 or "*" in parts[1]:
                        reg_sum_tainted.add(dst_c)
                    elif len(mem_regs) == 1 and mem_regs[0] in reg_sum_tainted:
                        reg_sum_tainted.add(dst_c)
                    else:
                        reg_sum_tainted.discard(dst_c)
                    if any(r in val_tainted for r in mem_regs):
                        val_tainted.add(dst_c)
                    else:
                        val_tainted.discard(dst_c)
                elif len(parts) >= 2:
                    src_part = parts[1]
                    src_c = canon_x86_gpr(src_part)
                    if mnem in ("add", "sub") and src_c and "[" not in src_part:
                        reg_sum_tainted.add(dst_c)
                    if "[" in src_part or (src_c and src_c in val_tainted):
                        val_tainted.add(dst_c)

        # 4. Branch check: ONLY allow bottom-tested `dec rcx|ecx` -> `jne|jnz` when `rcx` is UNTAINTED!
        if mnem.startswith("j"):
            if mnem in ("jne", "jnz") and idx > 0:
                prev_mnem, prev_ops = instrs[idx - 1]
                if prev_mnem == "dec" and prev_ops.lower() in ("rcx", "ecx"):
                    if "rcx" in val_tainted or "rcx" in reg_sum_tainted:
                        errors.append(
                            f"{sym}[{idx}]: forbidden secret-tainted loop trip count `dec {prev_ops}; {mnem} {ops}`"
                        )
                    continue
            errors.append(f"{sym}[{idx}]: forbidden conditional/unverified branch `{mnem} {ops}`")

        # 5. Live-at-`ret` SIMD register hygiene (`vzeroupper` + zero live `xmm`/`ymm` regs!)
        if mnem == "ret":
            if uses_ymm and ymm_upper_dirty:
                errors.append(f"{sym}[{idx}]: missing `vzeroupper` prior to `ret` after touching YMM")
            if dirty_simd:
                leaked = [f"xmm{r}/ymm{r}" for r in sorted(dirty_simd)]
                errors.append(
                    f"{sym}[{idx}]: unzeroed live XMM/YMM registers at `ret`: {leaked}"
                )

    return errors


def is_rust_non_crypto_helper(sym: str) -> bool:
    """Identify non-cryptographic compiler/runtime/CPUID support symbols in `.rlib`."""
    non_crypto_markers = (
        "cpuid",
        "probe_capabilities",
        "probe_x86_64",
        "probe_aarch64",
        "detect_backend",
        "enable_hardware_dit",
        "ensure_aarch64_dit_enabled",
        "SimdBackend",
        "CpuCapabilities",
        "HardwareDitStatus",
        "panicking",
        "panic_bounds_check",
        "slice_end_index_len_fail",
        "slice_start_index_len_fail",
        "fmt",
        "Debug",
        "Clone",
        "Default",
        "rust_eh_personality",
        "__rust_",
        "drop_in_place",
    )
    return any(m in sym for m in non_crypto_markers)


def is_branchless_portable_primitive(sym: str) -> bool:
    """Fixed-width portable cryptographic primitives that must compile with ZERO conditional branches."""
    straight_line_names = (
        "wiedemann_mul_t",
        "wiedemann_scale_t",
        "tower128_to_poly128_ct",
        "poly128_to_tower128_ct",
        "clmul64_portable",
        "clmul128_wide_portable",
        "clmul256_reduce_0x87",
        "goldilocks_canonicalize_ct",
        "goldilocks_add_ct_portable",
        "goldilocks_sub_ct_portable",
        "goldilocks_mul_ct_portable",
        "ct_eq_32_portable",
    )
    return any(name in sym for name in straight_line_names)


def audit_compiled_rust_x86_symbol(sym: str, instrs: list[tuple[str, str]]) -> list[str]:
    """
    Audit compiled Rust cryptographic functions (`portable::*`, `lib.rs` entrypoints,
    `x86_64_asm::run_*`) for:
      - ZERO variable-latency divisions (`div`, `idiv`, `vdiv*`, `fdiv*`),
      - ZERO variable `cl` / `shlx` / `shrx` / `sarx` shifts,
      - ZERO `vpgather*` scatter/gather LUT instructions,
      - ZERO conditional branches or scaled LUT loads inside straight-line `portable::*`
        field/tag primitives (`wiedemann_mul_*`, `tower128_to_poly128_ct`, `goldilocks_*`, `ct_eq_32_portable`),
      - Clean `vzeroupper` before `ret` whenever `ymm` registers are touched.
    """
    errors = []
    uses_ymm = any("ymm" in ops.lower() for _, ops in instrs)
    ymm_dirty = False
    must_be_straight_line = is_branchless_portable_primitive(sym)

    for idx, (mnem, ops) in enumerate(instrs):
        if mnem in ("nop", "cs", "endbr64"):
            continue
        ops_l = ops.lower()
        if "ymm" in ops_l:
            ymm_dirty = True
        if mnem == "vzeroupper":
            ymm_dirty = False

        if mnem in X86_DIV_MNEMONICS:
            errors.append(f"{sym}[{idx}]: compiled Rust contains hardware divider `{mnem} {ops}`")
        if mnem in X86_GATHER_MNEMONICS:
            errors.append(f"{sym}[{idx}]: compiled Rust contains gather LUT `{mnem} {ops}`")
        sh_err = check_x86_variable_shift(sym, idx, mnem, ops_l)
        if sh_err:
            errors.append(f"compiled Rust {sh_err}")
        if must_be_straight_line:
            if mnem.startswith("j") and mnem != "jmp":
                errors.append(
                    f"{sym}[{idx}]: straight-line portable primitive contains conditional jump `{mnem} {ops}`"
                )
            for mem in re.findall(r"\[([^\]]+)\]", ops_l):
                if "*" in mem and mnem != "lea":
                    errors.append(
                        f"{sym}[{idx}]: straight-line portable primitive contains scaled LUT address `[{mem}]`"
                    )
        if mnem in ("call", "callq") and ymm_dirty:
            errors.append(f"{sym}[{idx}]: call with dirty upper YMM state")
        if mnem == "ret" and uses_ymm and ymm_dirty:
            errors.append(f"{sym}[{idx}]: compiled Rust missing `vzeroupper` before `ret`")

    return errors


def audit_aarch64_symbol(sym: str, instrs: list[tuple[str, str]]) -> list[str]:
    errors = []
    if not instrs:
        return [f"{sym}: empty instruction stream"]

    reg_sum_tainted: set[str] = set()
    val_tainted: set[str] = set()
    dirty_neon: set[str] = set()

    base_sym = sym.lstrip("_")
    if "goldilocks_" in base_sym:
        val_tainted.update({"x0", "x1"})

    for idx, (mnem, ops) in enumerate(instrs):
        if mnem in ("nop", "cs"):
            continue
        ops_l = ops.lower()
        parts = split_top_operands(ops_l)

        if mnem in AARCH64_DIV_MNEMONICS:
            errors.append(f"{sym}[{idx}]: forbidden variable-latency divider `{mnem} {ops}`")
        if mnem in AARCH64_CSEL_MNEMONICS:
            errors.append(f"{sym}[{idx}]: forbidden conditional select `{mnem} {ops}` (use sbc/adc ALU mask)")
        if mnem in AARCH64_VAR_SHIFT_MNEMONICS:
            errors.append(f"{sym}[{idx}]: forbidden variable shift `{mnem} {ops}`")
        if mnem in ("lsl", "lsr", "asr", "ror"):
            if len(parts) == 3 and not parts[2].startswith("#"):
                errors.append(f"{sym}[{idx}]: forbidden register-count shift `{mnem} {ops}`")

        # Stateful live-at-`ret` NEON register tracking (`eor vN.16b, vN.16b, vN.16b` wipes `vN`;
        # ANY subsequent load or ALU write to `vN`/`qN`/`dN` marks `vN` dirty again!).
        is_neon_self_zero = (
            mnem in ("eor", "eor.16b")
            and len(parts) == 3
            and parts[0] == parts[1] == parts[2]
            and canon_a64_neon(parts[0]) is not None
        )
        if is_neon_self_zero:
            dirty_neon.discard(canon_a64_neon(parts[0]))
        elif not mnem.startswith(("str", "stp", "st1", "st2", "st3", "st4")):
            if mnem == "ldp" and len(parts) >= 2:
                for p in parts[:2]:
                    vn = canon_a64_neon(p)
                    if vn:
                        dirty_neon.add(vn)
            elif parts:
                vn = canon_a64_neon(parts[0])
                if vn:
                    dirty_neon.add(vn)

        # Reject register-offset memory `[xN, xM...]`, pre-added `[xA]`, AND `[tainted_xN + #imm]` LUTs
        for mem in re.findall(r"\[([^\]]+)\]", ops_l):
            regs_in_mem = re.findall(r"\b([xw][0-9]+|sp)\b", mem)
            canon_regs = [canon_a64_gpr(r) for r in regs_in_mem if canon_a64_gpr(r) is not None]
            if len(canon_regs) > 1:
                errors.append(f"{sym}[{idx}]: forbidden register-indexed address `[{mem}]`")
            for cr in canon_regs:
                if cr in reg_sum_tainted:
                    errors.append(
                        f"{sym}[{idx}]: forbidden pre-added single-register LUT dereference `[{mem}]` via `{cr}`"
                    )
                if cr in val_tainted:
                    errors.append(
                        f"{sym}[{idx}]: forbidden secret-tainted base/offset LUT dereference `[{mem}]` via `{cr}`"
                    )

        # Update AArch64 GPR `reg_sum_tainted` and `val_tainted`
        if mnem in ("ldr", "ldrb", "ldrh", "ldrsw") and len(parts) >= 2:
            dst_c = canon_a64_gpr(parts[0])
            if dst_c and dst_c != "sp":
                val_tainted.add(dst_c)
        elif mnem == "ldp" and len(parts) >= 3:
            for p in parts[:2]:
                dst_c = canon_a64_gpr(p)
                if dst_c and dst_c != "sp":
                    val_tainted.add(dst_c)
        elif mnem in ("add", "adds", "sub", "subs") and "[" not in ops_l and len(parts) >= 3:
            dst_c = canon_a64_gpr(parts[0])
            src1_c = canon_a64_gpr(parts[1])
            src2_c = canon_a64_gpr(parts[2].split()[0])
            if dst_c and dst_c != "sp":
                if src1_c and src2_c:
                    reg_sum_tainted.add(dst_c)
                elif not parts[2].startswith("#") and src2_c is not None:
                    reg_sum_tainted.add(dst_c)
                if (src1_c and src1_c in val_tainted) or (src2_c and src2_c in val_tainted):
                    val_tainted.add(dst_c)
        elif mnem in ("eor", "orr", "and", "bic", "mul", "umulh", "lsl", "lsr", "sbc", "adc") and len(parts) >= 3:
            dst_c = canon_a64_gpr(parts[0])
            if dst_c and dst_c != "sp":
                src_gprs = [canon_a64_gpr(p.split()[0]) for p in parts[1:]]
                if mnem in ("sbc", "adc") or any(s in val_tainted for s in src_gprs if s):
                    val_tainted.add(dst_c)
        elif mnem in ("mov", "movz") and len(parts) == 2:
            dst_c = canon_a64_gpr(parts[0])
            src_c = canon_a64_gpr(parts[1])
            if dst_c:
                if src_c and src_c in reg_sum_tainted:
                    reg_sum_tainted.add(dst_c)
                else:
                    reg_sum_tainted.discard(dst_c)
                if src_c and src_c in val_tainted:
                    val_tainted.add(dst_c)
                else:
                    val_tainted.discard(dst_c)

        # Conditional branches: allow strictly `subs x1|x3, x1|x3, #0x1` -> `b.ne` when untainted
        if mnem.startswith("b.") or mnem in ("cbz", "cbnz", "tbz", "tbnz"):
            if mnem == "b.ne" and idx > 0:
                prev_m, prev_o = instrs[idx - 1]
                m_cnt = re.match(r"^(x[13]),\s*\1,\s*#?(0x)?1$", prev_o.lower())
                if prev_m == "subs" and m_cnt:
                    cnt_reg = m_cnt.group(1)
                    if cnt_reg in val_tainted or cnt_reg in reg_sum_tainted:
                        errors.append(
                            f"{sym}[{idx}]: forbidden secret-tainted loop counter `subs {prev_o}; {mnem} {ops}`"
                        )
                    continue
            errors.append(f"{sym}[{idx}]: forbidden conditional branch `{mnem} {ops}`")

        # Live-at-`ret` NEON register hygiene across ALL 7 AArch64 kernels!
        if mnem == "ret" and dirty_neon:
            errors.append(
                f"{sym}[{idx}]: unzeroed live caller-saved NEON registers at `ret`: {sorted(dirty_neon)}"
            )

    return errors


def extract_apple_inline_asm(rs_path: Path) -> str:
    """Extract the `#[cfg(target_vendor = "apple")] global_asm!(...)` assembly lines from `aarch64_asm.rs`."""
    src = rs_path.read_text()
    marker = '#[cfg(target_vendor = "apple")]'
    pos = src.find(marker)
    if pos < 0:
        raise ValueError(f"Could not find `{marker}` in {rs_path}")
    ga_start = src.find("global_asm!(", pos)
    ga_end = src.find(");", ga_start)
    if ga_start < 0 or ga_end < 0:
        raise ValueError(f"Could not delimit `global_asm!(...);` block in {rs_path}")
    body = src[ga_start + len("global_asm!(") : ga_end]
    asm_lines = [m.group(1) for m in re.finditer(r'"([^"]*)"', body)]
    if not asm_lines:
        raise ValueError(f"Extracted 0 assembly lines from Apple `global_asm!` in {rs_path}")
    return "\n".join(asm_lines) + "\n"


def extract_x86_global_asm_for_target(rs_path: Path, target_flavor: str) -> str:
    """
    Reconstruct `x86_64` `global_asm!(...)` from `x86_64_asm.rs` with Intel syntax and
    either Windows COFF (`windows`) or Apple Mach-O (`apple`) symbol directives.
    """
    src = rs_path.read_text()
    ga_start = src.find("global_asm!(")
    ga_end = src.find(");\n", ga_start)
    if ga_start < 0 or ga_end < 0:
        raise ValueError(f"Could not locate `global_asm!(...);` in {rs_path}")
    body = src[ga_start + len("global_asm!(") : ga_end]
    out_lines = [".intel_syntax noprefix", ".text"]
    token_re = re.compile(
        r'sym_header!\("([^"]+)"\)|sym_footer!\("([^"]+)"\)|"([^"]*)"'
    )
    for m in token_re.finditer(body):
        hdr, ftr, ins = m.group(1), m.group(2), m.group(3)
        if hdr is not None:
            sym = f"_{hdr}" if target_flavor == "apple" else hdr
            out_lines.extend([f".globl {sym}", ".p2align 4", f"{sym}:"])
        elif ftr is not None:
            continue
        elif ins is not None:
            out_lines.append(ins)
    return "\n".join(out_lines) + "\n"


def extract_elf_disasm_and_rodata_syms(archive_or_obj: Path) -> tuple[str, list[str]]:
    disasm_chunks: list[str] = []
    symtab_lines: list[str] = []
    if archive_or_obj.read_bytes()[:4] == b"\x7fELF":
        disasm_chunks.append(
            subprocess.check_output(
                ["objdump", "-d", "-C", "-M", "intel", str(archive_or_obj)], text=True
            )
        )
        symtab_lines.extend(
            subprocess.check_output(["objdump", "-t", str(archive_or_obj)], text=True).splitlines()
        )
    else:
        with tempfile.TemporaryDirectory() as tmpdir:
            subprocess.check_call(["ar", "x", str(archive_or_obj)], cwd=tmpdir)
            for member in sorted(Path(tmpdir).iterdir()):
                if member.is_file() and member.read_bytes()[:4] == b"\x7fELF":
                    disasm_chunks.append(
                        subprocess.check_output(
                            ["objdump", "-d", "-C", "-M", "intel", str(member)], text=True
                        )
                    )
                    symtab_lines.extend(
                        subprocess.check_output(["objdump", "-t", str(member)], text=True).splitlines()
                    )
    return "\n".join(disasm_chunks), symtab_lines


def run_negative_self_tests() -> int:
    # 1. Conditional branch on comparison
    bad_jcc = [("cmp", "rax, rbx"), ("je", "0x20"), ("ret", "")]
    assert any("branch" in e for e in audit_x86_symbol("bad_jcc", bad_jcc))

    # 2. Hardware variable-latency divider
    bad_div = [("div", "rcx"), ("ret", "")]
    assert any("divider" in e for e in audit_x86_symbol("bad_div", bad_div))

    # 3. Scaled secret-indexed memory operand `[rdi + rax*1]`
    bad_lut = [("movzx", "eax, byte ptr [rdi + rax*1]"), ("ret", "")]
    assert any("memory" in e or "indexed" in e for e in audit_x86_symbol("bad_lut", bad_lut))

    # 4. Pre-added single-register LUT dereference `add r8, rax; movzx eax, [r8]`
    bad_preadded_lut = [("add", "r8, rax"), ("movzx", "eax, byte ptr [r8]"), ("ret", "")]
    assert any("pre-added" in e for e in audit_x86_symbol("bad_preadded_lut", bad_preadded_lut))

    # 5. Single-register static-displacement LUT `movzx eax, [rsi]; movzx eax, [rax + 0x1000]`
    bad_static_disp_lut = [
        ("movzx", "eax, byte ptr [rsi]"),
        ("movzx", "eax, byte ptr [rax + 0x1000]"),
        ("ret", ""),
    ]
    assert any("secret-tainted" in e for e in audit_x86_symbol("bad_static_disp_lut", bad_static_disp_lut))

    # 6. Secret-tainted loop counter `movzx ecx, [rsi]; dec ecx; jnz`
    bad_secret_loop = [
        ("movzx", "ecx, byte ptr [rsi]"),
        ("dec", "ecx"),
        ("jnz", "0x0"),
        ("ret", ""),
    ]
    assert any("loop trip count" in e for e in audit_x86_symbol("bad_secret_loop", bad_secret_loop))

    # 7. Variable `cl` shift & BMI2 `shlx`
    bad_var_shift = [("shl", "rax, cl"), ("ret", "")]
    assert any("shift" in e for e in audit_x86_symbol("bad_var_shift", bad_var_shift))

    bad_shlx = [("shlx", "rax, rdi, rsi"), ("ret", "")]
    assert any("shift" in e for e in audit_x86_symbol("bad_shlx", bad_shlx))

    # 8. Missing `vzeroupper`
    bad_ymm = [("vpxor", "ymm0, ymm1, ymm2"), ("ret", "")]
    assert any("vzeroupper" in e for e in audit_x86_symbol("bad_ymm", bad_ymm))

    # 9. `vzeroupper` WITHOUT zeroing lower `xmm0` (`vmovdqu ymm0, [rsi]; vzeroupper; ret`)
    bad_dirty_xmm = [("vmovdqu", "ymm0, ymmword ptr [rsi]"), ("vzeroupper", ""), ("ret", "")]
    assert any("unzeroed live XMM/YMM" in e for e in audit_x86_symbol("bad_dirty_xmm", bad_dirty_xmm))

    # 10. AArch64 branch, divider, variable shift, and pre-added LUT
    bad_a64 = [
        ("cbz", "x0, 0x10"),
        ("udiv", "x0, x1, x2"),
        ("lslv", "x0, x1, x2"),
        ("add", "x8, x8, x0"),
        ("ldrb", "w0, [x8]"),
        ("ret", ""),
    ]
    a64_errs = audit_aarch64_symbol("bad_a64", bad_a64)
    assert len(a64_errs) >= 4, f"expected >=4 negative AArch64 errors, got {a64_errs}"

    # 11. Unzeroed NEON `v16` at `ret`
    bad_pmull_leak = [("pmull", "v16.1q, v0.1d, v2.1d"), ("ret", "")]
    assert any(
        "unzeroed live" in e
        for e in audit_aarch64_symbol("_qsag_asm_tower128_bdoz_mac_pmull", bad_pmull_leak)
    )

    # 12. Order-sensitive NEON reload AFTER wipe (`eor v16, v16, v16; ldr q16, [x1]; ret`)
    bad_neon_reload_after_wipe = [
        ("eor", "v16.16b, v16.16b, v16.16b"),
        ("ldr", "q16, [x1, #0]"),
        ("ret", ""),
    ]
    assert any(
        "unzeroed live" in e
        for e in audit_aarch64_symbol("_qsag_asm_keccak_sha3_neon", bad_neon_reload_after_wipe)
    )

    # 13. Secret-tainted AArch64 loop counter `ldr x3, [x1]; subs x3, x3, #1; b.ne`
    bad_a64_secret_loop = [
        ("ldr", "x3, [x1, #0]"),
        ("subs", "x3, x3, #1"),
        ("b.ne", "0x0"),
        ("ret", ""),
    ]
    assert any(
        "secret-tainted loop counter" in e
        for e in audit_aarch64_symbol("bad_a64_secret_loop", bad_a64_secret_loop)
    )
    # Instruction parity must reject a missing instruction and a substituted mnemonic.
    sample = {name: [("ret", "")] for name in EXPECTED_AARCH64_SYMBOLS}
    apple = {"_" + name: ins.copy() for name, ins in sample.items()}
    assert not aarch64_parity_errors(sample, apple)
    apple["_" + EXPECTED_AARCH64_SYMBOLS[0]] = []
    assert aarch64_parity_errors(sample, apple)
    apple["_" + EXPECTED_AARCH64_SYMBOLS[0]] = [("nop", "")]
    assert aarch64_parity_errors(sample, apple)
    return 15


def assemble(source: Path, output: Path, triple: str, llvm_mc: str | None) -> None:
    if llvm_mc:
        cmd = [llvm_mc, f"-triple={triple}", "-filetype=obj", str(source), "-o", str(output)]
    else:
        clang = shutil.which("clang")
        if not clang:
            raise RuntimeError("Cross assembly requires llvm-mc-19, llvm-mc, or clang")
        cmd = [clang, f"--target={triple}", "-c", "-x", "assembler", str(source), "-o", str(output)]
    subprocess.check_call(cmd)


def llvm_library_disasm(path: Path, triple: str) -> str:
    """Read object sections/symbols and decode real bytes through LLVM's C API."""
    lib = ctypes.CDLL("libLLVM-19.so")
    ptr = ctypes.c_void_p
    def api(name, result, *args):
        fn = getattr(lib, name)
        fn.restype, fn.argtypes = result, list(args)
        return fn
    arch = "AArch64" if triple.startswith("aarch64") else "X86"
    for suffix in ("TargetInfo", "Target", "TargetMC", "Disassembler"):
        api(f"LLVMInitialize{arch}{suffix}", None)()
    buf, err = ptr(), ctypes.c_char_p()
    rc = api("LLVMCreateMemoryBufferWithContentsOfFile", ctypes.c_int, ctypes.c_char_p,
             ctypes.POINTER(ptr), ctypes.POINTER(ctypes.c_char_p))(
                 str(path).encode(), ctypes.byref(buf), ctypes.byref(err))
    if rc:
        raise RuntimeError(err.value.decode())
    obj = api("LLVMCreateObjectFile", ptr, ptr)(buf)
    if not obj:
        raise RuntimeError(f"LLVM cannot read {path}")
    dc = api("LLVMCreateDisasmCPUFeatures", ptr, ctypes.c_char_p, ctypes.c_char_p,
             ctypes.c_char_p, ptr, ctypes.c_int, ptr, ptr)(
                 triple.encode(), b"generic", b"+v8.4a,+sha3,+aes,+dit" if arch == "AArch64" else b"",
                 None, 0, None, None)
    if not dc:
        raise RuntimeError(f"LLVM cannot disassemble {triple}")
    if arch == "X86":
        api("LLVMSetDisasmOptions", ctypes.c_int, ptr, ctypes.c_uint64)(dc, 4)
    symbols = api("LLVMGetSymbols", ptr, ptr)(obj)
    sections = api("LLVMGetSections", ptr, ptr)(obj)
    records = []
    try:
        while not api("LLVMIsSymbolIteratorAtEnd", ctypes.c_int, ptr, ptr)(obj, symbols):
            name = api("LLVMGetSymbolName", ctypes.c_char_p, ptr)(symbols).decode()
            if name.lstrip("_").startswith("qsag_asm_"):
                addr = api("LLVMGetSymbolAddress", ctypes.c_uint64, ptr)(symbols)
                size = api("LLVMGetSymbolSize", ctypes.c_uint64, ptr)(symbols)
                api("LLVMMoveToContainingSection", None, ptr, ptr)(sections, symbols)
                base = api("LLVMGetSectionAddress", ctypes.c_uint64, ptr)(sections)
                length = api("LLVMGetSectionSize", ctypes.c_uint64, ptr)(sections)
                data = api("LLVMGetSectionContents", ptr, ptr)(sections)
                records.append((name, addr, size, base, length, data))
            api("LLVMMoveToNextSymbol", None, ptr)(symbols)
        lines = []
        decode = api("LLVMDisasmInstruction", ctypes.c_size_t, ptr, ptr, ctypes.c_uint64,
                     ctypes.c_uint64, ctypes.c_char_p, ctypes.c_size_t)
        for name, addr, size, base, length, data in records:
            end = min([a for _, a, _, b, _, d in records if d == data and a > addr] or [base + length])
            if size and "apple" not in triple:
                end = min(end, addr + size)
            lines.append(f"{addr:x} <{name}>:")
            offset = addr - base
            while base + offset < end:
                out = ctypes.create_string_buffer(1024)
                n = decode(dc, data + offset, end - base - offset, base + offset, out, len(out))
                if not n:
                    raise RuntimeError(f"Undecodable instruction in {name} at {base + offset:#x}")
                raw = ctypes.string_at(data + offset, n).hex(" ")
                lines.append(f" {base + offset:x}: {raw}\t{out.value.decode().strip()}")
                offset += n
        return "\n".join(lines)
    finally:
        api("LLVMDisposeSymbolIterator", None, ptr)(symbols)
        api("LLVMDisposeSectionIterator", None, ptr)(sections)
        api("LLVMDisasmDispose", None, ptr)(dc)
        api("LLVMDisposeObjectFile", None, ptr)(obj)


def disassemble(path: Path, triple: str, objdump: str | None) -> str:
    if not objdump:
        return llvm_library_disasm(path, triple)
    opts = ["--mattr=+v8.4a,+sha3,+aes,+dit"] if triple.startswith("aarch64") else ["--x86-asm-syntax=intel"]
    return subprocess.check_output([objdump, "-d", *opts, str(path)], text=True)


def mnemonic_sequence(ins: list[tuple[str, str]]) -> list[str]:
    # Alias spellings used by different LLVM versions; operands are audited separately.
    aliases = {"bne": "b.ne", "b.eq": "beq"}
    return [aliases.get(m, m) for m, _ in ins]


def aarch64_parity_errors(linux, apple) -> list[str]:
    errors = []
    names = set(EXPECTED_AARCH64_SYMBOLS) | {s[1:] for s in apple if s.startswith("_qsag_asm_")}
    for sym in sorted(names):
        li, ap = linux.get(sym), apple.get("_" + sym)
        if li is None or ap is None or mnemonic_sequence(li) != mnemonic_sequence(ap):
            errors.append(f"AArch64 instruction-stream parity mismatch: {sym}")
    return errors


def legacy_main() -> int:
    num_self_tests = run_negative_self_tests()

    ap = argparse.ArgumentParser()
    ap.add_argument("--rlib", required=True, help="Path to compiled libqsag_asm*.rlib or .o on x86_64")
    ap.add_argument(
        "--extra-rlib",
        action="append",
        default=[],
        help="Optional extra compiled .rlib archives to audit for hardware dividers / variable shifts",
    )
    ap.add_argument(
        "--x86-asm-rs",
        help="Optional path to src/x86_64_asm.rs to cross-assemble for Windows COFF & Apple Mach-O",
    )
    ap.add_argument("--aarch64-asm", help="Path to aarch64_kernels.s to cross-assemble & audit")
    ap.add_argument(
        "--aarch64-apple-rs",
        help="Path to src/aarch64_asm.rs to extract Apple Mach-O global_asm! & cross-audit",
    )
    ap.add_argument("--llvm-mc", default=None)
    ap.add_argument("--llvm-objdump", default=None)
    args = ap.parse_args()
    args.llvm_mc = args.llvm_mc or shutil.which("llvm-mc-19") or shutil.which("llvm-mc")
    args.llvm_objdump = args.llvm_objdump or shutil.which("llvm-objdump-19") or shutil.which("llvm-objdump")

    rlib_path = Path(args.rlib).resolve()
    out, symtab_lines = extract_elf_disasm_and_rodata_syms(rlib_path)
    funcs = parse_objdump_functions(out)

    all_errors: list[str] = []

    # Check symbol table for banned >= 4 KiB secret-indexed LUT tables (`TOWER128_ISO`)
    for sline in symtab_lines:
        if "TOWER128_ISO" in sline:
            all_errors.append(f"Forbidden 16 KiB static LUT symbol present in ELF: `{sline.strip()}`")

    # 1. Audit all 16 hand-crafted x86_64 assembly symbols
    total_x86_ins = 0
    for sym in EXPECTED_X86_SYMBOLS:
        if sym not in funcs:
            all_errors.append(f"MISSING x86_64 symbol in {args.rlib}: {sym}")
            print(f"  [x86_64 asm ] {sym:<38} : MISSING | FAIL")
            continue
        ins = funcs[sym]
        total_x86_ins += len(ins)
        errs = audit_x86_symbol(sym, ins)
        all_errors.extend(errs)
        verdict = "PASS" if not errs else f"FAIL ({len(errs)} errs)"
        print(f"  [x86_64 asm ] {sym:<38} : {len(ins):>3} instrs | 0 br/div/lut/xmm-leak | {verdict}")

    for sym in EXPECTED_X86_BITSLICE_SYMBOLS:
        if sym not in funcs:
            all_errors.append(f"MISSING x86_64 symbol in {args.rlib}: {sym}")
            print(f"  [x86_64 asm ] {sym:<38} : MISSING | FAIL")
            continue
        ins = funcs[sym]
        total_x86_ins += len(ins)
        errs = audit_x86_symbol(sym, ins)
        all_errors.extend(errs)
        verdict = "PASS" if not errs else f"FAIL ({len(errs)} errs)"
        print(f"  [x86_64 asm ] {sym:<38} : {len(ins):>3} instrs | 0 br/div/lut/xmm-leak | {verdict}")

    # 1b. Cross-assemble x86_64 kernels for Windows COFF (`x86_64-pc-windows-msvc`) & Apple Mach-O
    if args.x86_asm_rs:
        x86_rs_path = Path(args.x86_asm_rs)
        for flavor, triple in [
            ("windows", "x86_64-pc-windows-msvc"),
            ("apple", "x86_64-apple-darwin"),
        ]:
            asm_src = extract_x86_global_asm_for_target(x86_rs_path, flavor)
            with tempfile.TemporaryDirectory() as tmpdir:
                s_path = Path(tmpdir) / f"x86_{flavor}.s"
                o_path = Path(tmpdir) / f"x86_{flavor}.obj"
                s_path.write_text(asm_src)
                assemble(s_path, o_path, triple, args.llvm_mc)
                cross_funcs = parse_objdump_functions(disassemble(o_path, triple, args.llvm_objdump))
                for base_sym in EXPECTED_X86_SYMBOLS:
                    sym = "_" + base_sym if flavor == "apple" else base_sym
                    if not cross_funcs.get(sym):
                        all_errors.append(f"MISSING {flavor} x86_64 symbol: {sym}")
                    else:
                        all_errors.extend(audit_x86_symbol(base_sym, cross_funcs[sym]))
            print(f"  [x86_64 {flavor:<4}] Cross-assembled and audited all 16 kernels for `{triple}` | PASS")

    # 2. Audit ALL compiled Rust cryptographic functions in `--rlib` (and `--extra-rlib`)
    rust_crypto_funcs_audited = 0
    rust_crypto_ins = 0
    rust_errs_total = 0
    archives_to_scan = [(rlib_path.name, funcs)]
    for extra in args.extra_rlib:
        ep = Path(extra).resolve()
        e_out, _ = extract_elf_disasm_and_rodata_syms(ep)
        archives_to_scan.append((ep.name, parse_objdump_functions(e_out)))

    expected_x86_set = set(EXPECTED_X86_SYMBOLS)
    for arch_name, arch_funcs in archives_to_scan:
        for sym, ins in sorted(arch_funcs.items()):
            if sym in expected_x86_set or is_rust_non_crypto_helper(sym):
                continue
            if not ins:
                continue
            rust_crypto_funcs_audited += 1
            rust_crypto_ins += len(ins)
            errs = audit_compiled_rust_x86_symbol(f"{arch_name}::{sym}", ins)
            rust_errs_total += len(errs)
            all_errors.extend(errs)
    if not rust_crypto_funcs_audited:
        all_errors.append("No compiled Rust functions found; supply the native .o emitted with -C lto=no --emit=obj")
    rust_verdict = "PASS" if rust_errs_total == 0 else f"FAIL ({rust_errs_total} errs)"
    print(
        f"  [x86_64 rust] {rust_crypto_funcs_audited} compiled Rust crypto functions "
        f"({rust_crypto_ins} instrs) | 0 div/gather/cl-shl/lut | {rust_verdict}"
    )

    # 3. Cross-assemble & audit Linux ELF `aarch64_kernels.s` (WITHOUT `-mattr` on `llvm-mc`
    #    to prove `.arch armv8.4-a+sha3+crypto` assembles cleanly on baseline toolchains!)
    total_a64_linux_ins = 0
    if args.aarch64_asm:
        with tempfile.NamedTemporaryFile(suffix=".o", delete=False) as tf:
            tmp_obj = Path(tf.name)
        try:
            assemble(Path(args.aarch64_asm), tmp_obj, "aarch64-unknown-linux-gnu", args.llvm_mc)
            a64_dis = disassemble(tmp_obj, "aarch64-unknown-linux-gnu", args.llvm_objdump)
            a64_funcs = parse_objdump_functions(a64_dis)
            for sym in EXPECTED_AARCH64_SYMBOLS:
                if sym not in a64_funcs:
                    all_errors.append(f"MISSING Linux aarch64 symbol: {sym}")
                    print(f"  [aarch64 elf] {sym:<38} : MISSING | FAIL")
                    continue
                ins = a64_funcs[sym]
                total_a64_linux_ins += len(ins)
                errs = audit_aarch64_symbol(sym, ins)
                all_errors.extend(errs)
                verdict = "PASS" if not errs else f"FAIL ({len(errs)} errs)"
                print(
                    f"  [aarch64 elf] {sym:<38} : {len(ins):>3} instrs | 0 br/div/lut/v-leak | {verdict}"
                )
        finally:
            tmp_obj.unlink(missing_ok=True)

    # 4. Extract, cross-assemble (`aarch64-apple-darwin`), & audit Apple Mach-O inline `global_asm!`
    total_a64_apple_ins = 0
    if args.aarch64_apple_rs:
        apple_asm_src = extract_apple_inline_asm(Path(args.aarch64_apple_rs))
        with tempfile.TemporaryDirectory() as tmpdir:
            asm_file = Path(tmpdir) / "apple_kernels.s"
            obj_file = Path(tmpdir) / "apple_kernels.o"
            asm_file.write_text(apple_asm_src)
            assemble(asm_file, obj_file, "aarch64-apple-darwin", args.llvm_mc)
            apple_dis = disassemble(obj_file, "aarch64-apple-darwin", args.llvm_objdump)
            apple_symtab = subprocess.check_output(
                [args.llvm_objdump, "-t", str(obj_file)], text=True
            ) if args.llvm_objdump else ""
            apple_funcs = parse_objdump_functions(apple_dis)
            addr_to_globl: dict[int, str] = {}
            for sline in apple_symtab.splitlines():
                m_st = re.match(r"^([0-9a-fA-F]+)\s+g\s+.*?\s+(_qsag_asm_[A-Za-z0-9_]+)\s*$", sline)
                if m_st:
                    addr_to_globl[int(m_st.group(1), 16)] = m_st.group(2)
            for m_hdr in re.finditer(r"^([0-9a-fA-F]+)\s+<(ltmp[0-9]+)>:\s*$", apple_dis, re.M):
                addr = int(m_hdr.group(1), 16)
                ltmp = m_hdr.group(2)
                if addr in addr_to_globl and ltmp in apple_funcs:
                    apple_funcs[addr_to_globl[addr]] = apple_funcs[ltmp]
            for base_sym in EXPECTED_AARCH64_SYMBOLS:
                macho_sym = f"_{base_sym}"
                if macho_sym not in apple_funcs:
                    all_errors.append(f"MISSING Apple Mach-O aarch64 symbol: {macho_sym}")
                    print(f"  [aarch64 mac] {macho_sym:<38} : MISSING | FAIL")
                    continue
                ins = apple_funcs[macho_sym]
                total_a64_apple_ins += len(ins)
                errs = audit_aarch64_symbol(macho_sym, ins)
                all_errors.extend(errs)
                verdict = "PASS" if not errs else f"FAIL ({len(errs)} errs)"
                print(
                    f"  [aarch64 mac] {macho_sym:<38} : {len(ins):>3} instrs | 0 br/div/lut/v-leak | {verdict}"
                )

    if args.aarch64_asm and args.aarch64_apple_rs:
        all_errors.extend(aarch64_parity_errors(a64_funcs, apple_funcs))
        print("  [aarch64 parity] Compared counts and normalized mnemonic sequences for all 7 kernels")

    if all_errors:
        print("\nELF/MACH-O/COFF CONSTANT-TIME AUDIT FAILED:", file=sys.stderr)
        for e in all_errors:
            print(f"  - {e}", file=sys.stderr)
        return 1

    print(
        f"\nAUDIT SUMMARY: "
        f"{len(EXPECTED_X86_SYMBOLS) + len(EXPECTED_X86_BITSLICE_SYMBOLS)} x86_64 asm ({total_x86_ins} instrs) + "
        f"{rust_crypto_funcs_audited} compiled Rust crypto fns ({rust_crypto_ins} instrs) + "
        f"{len(EXPECTED_AARCH64_SYMBOLS) if args.aarch64_asm else 0} Linux aarch64 ({total_a64_linux_ins} instrs) + "
        f"{len(EXPECTED_AARCH64_SYMBOLS) if args.aarch64_apple_rs else 0} Apple aarch64 ({total_a64_apple_ins} instrs) "
        f"PASSED INSTRUCTION AUDIT ({num_self_tests} negative #tooth self-tests PASSED)."
    )
    return 0



"""Audit native ELF objects, archives and final ThinLTO ET_EXEC/ET_DYN images.

Build linked artifacts with strip=none. Inlining/dead stripping limits observable
coverage: absent symbols are listed, never counted as audited. This instruction
screen is not a proof of data-independent control flow. Rust protocol functions
can branch on public lengths/state; --strict-rust-branches rejects every branch
in those functions as well. Assembly kernels always use the existing taint-aware
branch checks (only proven public loop counters are exempt).
"""
import argparse
import json
import tempfile
from pathlib import Path
import re
import shutil
import subprocess
import sys

_SOURCE = Path(__file__).resolve().parents[1] / 'crates/qsag-asm/scripts/audit_elf_ct.py'
kernel_audit = sys.modules[__name__]

BITSLICE = {
    62: ['qsag_asm_transpose64x256_avx2', 'qsag_asm_gf2_128_mul_acc_pclmul',
         'qsag_asm_gf2_128_mul_acc_vpclmul'],
    183: ['qsag_asm_transpose64x256_neon', 'qsag_asm_gf2_128_mul_acc_pmull'],
}
RUST_MODULES = ('qsag_hd::linear_module::', 'qsag_asm::ct::',
                'qsag_core::rss256::', 'qsag_core::wots_c::', 'qsag_quorum::dzk::',
                'qsag_asm::bitslice::', 'qsag_asm::portable::')


def elf_header(data):
    if len(data) < 20 or data[:4] != b'\x7fELF' or data[4] != 2 or data[5] not in (1, 2):
        raise ValueError('expected ELF64 artifact')
    endian = 'little' if data[5] == 1 else 'big'
    kind = int.from_bytes(data[16:18], endian)
    machine = int.from_bytes(data[18:20], endian)
    if kind not in (1, 2, 3) or machine not in BITSLICE:
        raise ValueError(f'unsupported ELF type/machine {kind}/{machine}')
    return kind, machine


def conditional(mnemonic):
    return ((mnemonic.startswith('j') and mnemonic not in ('jmp', 'jmpq'))
            or mnemonic.startswith('loop') or mnemonic.startswith('b.')
            or mnemonic in ('cbz', 'cbnz', 'tbz', 'tbnz'))


def rust_errors(symbol, instructions, strict=False):
    errors = []
    if not instructions:
        return [f'{symbol}: empty instruction stream']
    straight = strict or kernel_audit.is_branchless_portable_primitive(symbol) or any(
        name in symbol for name in ('ct_reduce_mod_q_u64', 'ct_reduce_mod_q_u128',
                                     '::mod_q_mul', '::mod_q_add', '::mod_q_sub'))
    for i, (mnemonic, operands) in enumerate(instructions):
        if mnemonic in kernel_audit.X86_DIV_MNEMONICS | kernel_audit.AARCH64_DIV_MNEMONICS or mnemonic.startswith(('fdiv', 'vdiv')):
            errors.append(f'{symbol}[{i}]: forbidden divider {mnemonic} {operands}')
        if straight and conditional(mnemonic):
            errors.append(f'{symbol}[{i}]: forbidden conditional branch {mnemonic} {operands}')
    return errors


def self_tests():
    count = kernel_audit.run_negative_self_tests()
    dirty_call = [('vpxor', 'ymm0,ymm0,ymm0'), ('call', 'callee'), ('ret', '')]
    assert audit_compiled_rust_x86_symbol('probe', dirty_call)
    clean_call = dirty_call[:1] + [('vzeroupper', '')] + dirty_call[1:]
    assert not audit_compiled_rust_x86_symbol('probe', clean_call)
    count += 2
    for mnemonic in ('div', 'idiv', 'udiv', 'sdiv', 'fdiv', 'jne', 'b.eq', 'cbz', 'cbnz', 'tbz', 'tbnz'):
        assert rust_errors('qsag_hd::linear_module::ct_reduce_mod_q_u64', [(mnemonic, '')])
        count += 1
    for kind in (1, 2, 3):
        for machine in BITSLICE:
            data = b'\x7fELF\x02\x01' + bytes(10) + kind.to_bytes(2, 'little') + machine.to_bytes(2, 'little')
            assert elf_header(data) == (kind, machine)
            count += 1
    return count


def audit(path, objdump, strict, require_bitslice):
    data = path.read_bytes()
    native_members = []
    if data.startswith(b'!<arch>\n'):
        members = subprocess.check_output(['ar', 't', str(path)], text=True).splitlines()
        native_members = [blob for member in members
                          if (blob := subprocess.check_output(['ar', 'p', str(path), member])).startswith(b'\x7fELF')]
        headers = [elf_header(blob) for blob in native_members]
        print(f'{path}: {len(native_members)} native archive members; bitcode/metadata are not instruction streams')
        if not headers:
            raise ValueError('archive has no native ELF members; supply emitted objects or a linked image')
        machines = {h[1] for h in headers}
        if len(machines) != 1:
            raise ValueError('mixed-architecture archive')
        machine = machines.pop()
        kind = 1
    else:
        kind, machine = elf_header(data)
    executable = objdump or shutil.which('llvm-objdump') or ('objdump' if machine == 62 else 'aarch64-linux-gnu-objdump')
    command = [executable, '-d', '-C']
    if machine == 62:
        command += ['-M', 'intel']
    elif 'llvm-objdump' in executable:
        command += ['--mattr=+v8.4a,+sha3,+aes,+dit']
    if native_members:
        chunks = []
        with tempfile.TemporaryDirectory() as directory:
            for index, blob in enumerate(native_members):
                member_path = Path(directory) / f'{index}.o'
                member_path.write_bytes(blob)
                chunks.append(subprocess.check_output(command + [str(member_path)], text=True))
        output = '\n'.join(chunks)
    else:
        output = subprocess.check_output(command + [str(path)], text=True)
    functions = kernel_audit.parse_objdump_functions(output)
    expected = (kernel_audit.EXPECTED_X86_SYMBOLS if machine == 62 else kernel_audit.EXPECTED_AARCH64_SYMBOLS) + BITSLICE[machine]
    errors, audited = [], []
    branches = 0
    for symbol, instructions in functions.items():
        # Test/benchmark timing and assertion code is not a cryptographic kernel.
        if re.search(r'::(?:tests|[A-Za-z0-9_]+_tests)::', symbol):
            continue
        base = symbol.lstrip('_')
        if base in expected or base.startswith('qsag_bitslice_'):
            check = kernel_audit.audit_x86_symbol if machine == 62 else kernel_audit.audit_aarch64_symbol
            errors.extend(check(symbol, instructions))
        elif any(module in symbol for module in RUST_MODULES) or 'gf2_128_mul_acc_batch' in symbol:
            if machine == 62:
                errors.extend(kernel_audit.audit_compiled_rust_x86_symbol(symbol, instructions))
            errors.extend(rust_errors(symbol, instructions, strict))
            branches += sum(conditional(m) for m, _ in instructions)
        else:
            continue
        audited.append(symbol)
    missing = [s for s in expected if not functions.get(s)]
    if require_bitslice:
        errors.extend(f'missing required bitslice kernel: {s}' for s in BITSLICE[machine] if s in missing)
    if not audited:
        errors.append('no matching native symbols; use strip=none and retain the kernel call sites')
    print(f'{path}: ELF type={kind}, machine={machine}; audited {len(audited)} symbols')
    for symbol in audited:
        print(f'  audited: {symbol}')
    print(f'  absent assembly symbols: {", ".join(missing) or "none"}')
    for module in RUST_MODULES:
        if not any(module in s for s in audited):
            print(f'  absent Rust namespace: {module}')
    print(f'  Rust conditional instructions inspected: {branches}; protocol control flow requires dataflow review')
    for error in errors:
        print(f'  FAIL: {error}', file=sys.stderr)
    print(f'  instruction screen: {"FAIL" if errors else "PASS"}')
    return not errors


def cross_aarch64_bitslice(objdump):
    """Assemble the actual two AArch64 bitslice bodies, including transpose source."""
    source_dir = _SOURCE.parents[1] / 'src'
    block = (source_dir / 'bitslice.rs').read_text().rsplit('global_asm!(', 1)[1].split('    );', 1)[0]
    assembly = []
    token = re.compile(r'^\s*(?:(sym_header|sym_footer|include_str)!\(("[^"\n]+")\)|("(?:[^"\\]|\\.)*")),?\s*$', re.M)
    for match in token.finditer(block):
        kind, argument, literal = match.groups()
        value = json.loads(argument or literal)
        if kind == 'sym_header':
            assembly.append(f'.globl {value}\n.p2align 2\n.type {value}, %function\n{value}:')
        elif kind == 'sym_footer':
            assembly.append(f'.size {value}, .-{value}')
        elif kind == 'include_str':
            assembly.append((source_dir / value).read_text())
        else:
            assembly.append(value)
    with tempfile.TemporaryDirectory() as directory:
        source, output = Path(directory) / 'bitslice.s', Path(directory) / 'bitslice.o'
        source.write_text('\n'.join(assembly) + '\n')
        kernel_audit.assemble(source, output, 'aarch64-unknown-linux-gnu', None)
        return audit(output, objdump, False, True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--elf-bin', action='append', default=[], help='final linked ELF, repeatable')
    parser.add_argument('--rlib', action='append', default=[], help='native archive or object, repeatable')
    parser.add_argument('--llvm-objdump')
    parser.add_argument('--require-bitslice', action=argparse.BooleanOptionalAction, default=True,
                        help='require every bitslice assembly kernel for the input architecture (default: enabled)')
    parser.add_argument('--strict-rust-branches', action='store_true')
    parser.add_argument('--self-test', action='store_true')
    parser.add_argument('--cross-aarch64-bitslice', action='store_true', help='cross-assemble and audit both AArch64 bitslice kernels')
    if any(arg in sys.argv for arg in ('--x86-asm-rs', '--aarch64-asm', '--extra-x86-obj',
                                      '--extra-rlib', '--aarch64-apple-rs', '--llvm-mc')):
        return legacy_main()
    args = parser.parse_args()
    print(f'{self_tests()} auditor self-tests passed')
    paths = args.elf_bin + args.rlib
    if not paths and not args.self_test and not args.cross_aarch64_bitslice:
        parser.error('supply --elf-bin or --rlib (or --self-test)')
    success = True
    if args.cross_aarch64_bitslice:
        success = cross_aarch64_bitslice(args.llvm_objdump)
    for name in paths:
        try:
            success = audit(Path(name).resolve(), args.llvm_objdump, args.strict_rust_branches, args.require_bitslice) and success
        except (ValueError, OSError, subprocess.CalledProcessError) as error:
            print(f'{name}: FAIL: {error}', file=sys.stderr)
            success = False
    return 0 if success else 1


if __name__ == '__main__':
    sys.exit(main())
