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
     in asm kernels; compiled Rust rejects secret-dependent counts.
  5. ZERO secret-indexed or secret-tainted memory operands (`[base + idx*scale]`, `[reg1 + reg2]`,
     `vpgather*`, pre-added `[regA]` LUT dereferences, or static-displacement `[tainted_reg + disp]`
     LUT loads) in asm kernels, and ZERO >= 4 KiB static LUT symbols (`TOWER128_ISO`).
  6. Stateful live-at-`ret` SIMD register hygiene:
     - `x86_64`: tracks BOTH `ymm_upper_dirty` (`vzeroupper` required) AND `dirty_simd` (`xmm0..15` /
       `ymm0..15` must all be explicitly zeroized before `ret`; `vzeroupper` alone does NOT clear
       lower `xmm` halves, and reloading after a wipe re-marks the register dirty!).
     - `aarch64`: stateful `dirty_neon` (`v0..v31`) live-at-`ret` tracking across ALL 7 kernels
       (reloading a `qN`/`vN` register after `eor vN.16b, vN.16b, vN.16b` re-dirties `vN`!).
     - compiled Rust: every `target_feature` SIMD kernel, everything in `qsag_asm::bitslice` and
       `qsag_asm::linear_map`, and the register-wipe helpers must reach each `ret` and tail jump
       with every caller-saved vector register they wrote zeroed (`xmm`/`ymm`/`zmm0..31`, where
       `vzeroupper` and `vzeroall` do not cover `zmm16..31`; `v0..v7`, `v16..v31`). The check
       follows the function's control-flow graph, so a wipe on one arm of a branch does not
       cover the other. Other compiled Rust is counted and reported, not checked.
  7. Negative `#tooth` self-tests (including 48 vector-to-scalar taint mutations) verifying immediate rejection of
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
    "rax": "rax", "eax": "rax", "ax": "rax", "al": "rax", "ah": "rax",
    "rbx": "rbx", "ebx": "rbx", "bx": "rbx", "bl": "rbx", "bh": "rbx",
    "rcx": "rcx", "ecx": "rcx", "cx": "rcx", "cl": "rcx", "ch": "rcx",
    "rdx": "rdx", "edx": "rdx", "dx": "rdx", "dl": "rdx", "dh": "rdx",
    "rsi": "rsi", "esi": "rsi", "si": "rsi", "sil": "rsi",
    "rdi": "rdi", "edi": "rdi", "di": "rdi", "dil": "rdi",
    "rbp": "rbp", "ebp": "rbp", "bp": "rbp", "bpl": "rbp",
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
    t = re.sub(r"\[[0-9]+\]$", "", t)
    m = re.match(r"^(?:v([0-9]+)\.[0-9a-z]+|[qdsbh]([0-9]+))$", t)
    if m:
        idx = m.group(1) or m.group(2)
        return f"v{idx}"
    return None


def expand_a64_neon_list(ops_l: str) -> list[str]:
    out: list[str] = []
    for grp in re.findall(r"\{([^}]*)\}", ops_l):
        for item in grp.split(","):
            item = item.strip()
            if "-" in item:
                lo_s, hi_s = [s.strip() for s in item.split("-", 1)]
                lo_v, hi_v = canon_a64_neon(lo_s), canon_a64_neon(hi_s)
                if lo_v and hi_v:
                    lo_i, hi_i = int(lo_v[1:]), int(hi_v[1:])
                    n = ((hi_i - lo_i) % 32) + 1
                    for k in range(n):
                        out.append(f"v{(lo_i + k) % 32}")
            else:
                v = canon_a64_neon(item)
                if v:
                    out.append(v)
    return out


class InstructionStream(list):
    """Disassembly plus addresses and relocation identities, never guessed from offsets."""
    def __init__(self):
        super().__init__()
        self.addresses = []
        self.relocations = {}


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
            funcs.setdefault(current_sym, InstructionStream())
            continue
        if current_sym is None:
            continue
        relocation = re.match(r"^\s*[0-9a-fA-F]+:\s+R_[A-Z0-9_]+\s+(.+)$", raw_line)
        if relocation and funcs[current_sym]:
            funcs[current_sym].relocations[len(funcs[current_sym]) - 1] = relocation[1]
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
            funcs[current_sym].addresses.append(int(raw_line.strip().split(":", 1)[0], 16))
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

    uses_ymm = any("ymm" in ops.lower() or "zmm" in ops.lower() for _, ops in instrs)
    ymm_upper_dirty = False
    dirty_simd: set[int] = set()
    reg_sum_tainted: set[str] = set()

    # Seed value-tainted GPRs for scalar value-argument kernels
    val_tainted: set[str] = set()
    vector_tainted: set[int] = set(range(32))
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

        # Track upper-YMM/ZMM penalty state & live-at-ret XMM/YMM/ZMM register dirtiness
        if "ymm" in ops_l or "zmm" in ops_l:
            ymm_upper_dirty = True
        if mnem == "vzeroupper":
            # `vzeroupper` clears ONLY bits [511:128], NOT lower 128-bit `xmm0..xmm31`!
            ymm_upper_dirty = False

        if parts and "[" not in parts[0]:
            dst_simd = canon_x86_simd(parts[0])
            if dst_simd is not None:
                is_self_zero = (
                    (mnem in ("vpxor", "vpxorq", "vpxord", "vxorps", "vxorpd") and len(parts) == 3 and parts[0] == parts[1] == parts[2])
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

        # Transfers through XMM/YMM must preserve secrecy in both directions.
        if parts and "[" not in parts[0]:
            vd = canon_x86_simd(parts[0])
            sources = parts[1:]
            secret_source = any("[" in p or canon_x86_gpr(p) in val_tainted
                                or canon_x86_simd(p) in vector_tainted for p in sources)
            if vd is not None:
                zero = (mnem in ("pxor", "xorps", "xorpd") and len(parts) == 2
                        and parts[0] == parts[1]) or (
                        mnem in ("vpxor", "vpxorq", "vpxord", "vxorps", "vxorpd") and len(parts) == 3
                        and parts[1] == parts[2])
                if zero:
                    vector_tainted.discard(vd)
                elif secret_source:
                    vector_tainted.add(vd)
            elif any(canon_x86_simd(p) is not None for p in sources):
                gd = canon_x86_gpr(parts[0])
                if gd:
                    if secret_source:
                        val_tainted.add(gd)
                    elif mnem in ('movd', 'movq', 'vmovd', 'vmovq', 'pmovmskb',
                                  'vpmovmskb', 'pextrw', 'pextrd', 'pextrq',
                                  'vpextrw', 'vpextrd', 'vpextrq'):
                        val_tainted.discard(gd)

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
    )
    if any(m in sym for m in non_crypto_markers):
        return True
    # Destructors are storage management, except those of the secret-erasing guards: their
    # glue is the code that walks and wipes the secret, so it is screened like a kernel.
    if "drop_in_place" in sym or "drop_glue" in sym:
        return not is_secret_guard_drop(sym)
    return False


def is_secret_guard_drop(sym: str) -> bool:
    return bool(re.search(r"drop_(?:in_place|glue)::<qsag_asm::wipe::Secret", sym))


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


def audit_compiled_rust_x86_symbol(sym: str, instrs: list[tuple[str, str]], strict=False) -> list[str]:
    """Check upper-YMM/ZMM hygiene and the shared architecture-aware taint screen."""
    errors = []
    ymm_dirty = False
    for idx, (mnem, ops) in enumerate(instrs):
        ops_l = ops.lower()
        if "ymm" in ops_l or "zmm" in ops_l:
            ymm_dirty = True
        if mnem in ("vzeroupper", "vzeroall"):
            ymm_dirty = False
        if mnem in ("call", "callq", "ret") and ymm_dirty:
            errors.append(f"{sym}[{idx}]: call/return with dirty upper YMM/ZMM state")
    return errors + vector_wipe_errors(sym, instrs, 62) + rust_errors(sym, instrs, strict, machine=62)


def audit_compiled_rust_aarch64_symbol(sym: str, instrs: list[tuple[str, str]], strict=False) -> list[str]:
    """Caller-saved NEON (`v0..v7`, `v16..v31`) wipe on every SIMD kernel, plus the shared taint screen.

    The wipe check does not depend on `strict`: a kernel that leaves a register is a finding in
    every mode.
    """
    return vector_wipe_errors(sym, instrs, 183) + rust_errors(sym, instrs, strict, machine=183)


# Compiled Rust functions that must return, or tail-call, with every caller-saved vector
# register they wrote zeroed again: the `target_feature` kernels, everything in `bitslice` and
# `linear_map` (dispatchers and portable fallbacks included), and the register-wipe helpers
# themselves. The remaining compiled Rust (portable code elsewhere that LLVM vectorizes on its
# own) carries no such wipe; `audit` counts those functions and reports the number instead of
# passing them silently.
SIMD_KERNEL_MARKERS = (
    'qsag_asm::aarch64_simd::',
    'qsag_asm::linear_map::',
    'qsag_asm::avx512::',
    'qsag_asm::gf256_simd::',
    'qsag_asm::ntt_simd::x86_simd::',
    'qsag_asm::sha2_hw::sha256_compress_blocks_shani',
    'qsag_asm::sha2_hw::sha256_compress_blocks_aarch64_sha2',
    'qsag_asm::bitslice::',
    'qsag_asm::wipe::wipe_xmm_regs',
    'qsag_asm::wipe::wipe_ymm_regs',
    'qsag_asm::wipe::wipe_zmm_regs',
)

# First operand is a vector register that the instruction only reads.
X86_VECTOR_READ_ONLY = {
    'ptest', 'vptest', 'vtestps', 'vtestpd', 'comiss', 'comisd', 'ucomiss', 'ucomisd',
    'vcomiss', 'vcomisd', 'vucomiss', 'vucomisd',
}
A64_VECTOR_READ_ONLY = {'fcmp', 'fcmpe', 'fccmp', 'fccmpe'}


def is_simd_kernel_symbol(symbol):
    return (any(marker in symbol for marker in SIMD_KERNEL_MARKERS)
            and 'enter_aarch64_dit_region' not in symbol)


def vector_register_effect(mnemonic, operands, machine):
    """`(written, zeroed)` vector registers of one instruction, as register numbers.

    A register counts as zeroed only by an unmasked full self-XOR (or, on AArch64, an all-zero
    `movi`); every other write, masked writes included, leaves it dirty. `vzeroall` zeroes
    `0..15` only and `vzeroupper` zeroes nothing whole, so `zmm16..zmm31` need their own XOR.
    """
    op = operands.lower()
    if machine == 62:
        if mnemonic == 'vzeroall':
            return set(), set(range(16))
        parts = split_top_operands(op)
        if not parts or '[' in parts[0] or mnemonic in X86_VECTOR_READ_ONLY:
            return set(), set()
        masked = '{' in parts[0]
        destination = canon_x86_simd(re.sub(r'\s*\{[^}]*\}', '', parts[0]))
        if destination is None:
            return set(), set()
        zero = not masked and (
            (mnemonic in ('pxor', 'xorps', 'xorpd') and len(parts) == 2 and parts[0] == parts[1])
            or (mnemonic in ('vpxor', 'vpxorq', 'vpxord', 'vxorps', 'vxorpd') and len(parts) == 3
                and parts[1] == parts[2] and canon_x86_simd(parts[1]) is not None))
        return (set(), {destination}) if zero else ({destination}, set())
    if mnemonic.startswith(('str', 'stur', 'stp', 'st1', 'st2', 'st3', 'st4')) or (
            mnemonic in A64_VECTOR_READ_ONLY):
        return set(), set()
    parts = split_top_operands(op)
    if mnemonic.startswith(('ld1', 'ld2', 'ld3', 'ld4')):
        names = expand_a64_neon_list(op) or [canon_a64_neon(parts[0])] if parts else []
    elif mnemonic == 'ldp':
        names = [canon_a64_neon(p) for p in parts[:2]]
    else:
        names = [canon_a64_neon(parts[0])] if parts else []
    registers = {int(name[1:]) for name in names if name}
    if not registers:
        return set(), set()
    zero = len(parts) >= 2 and (
        (mnemonic == 'eor' and len(parts) == 3 and parts[0] == parts[1] == parts[2]
         and parts[0].endswith('.16b'))
        or (mnemonic == 'movi' and re.fullmatch(r'#(?:0x)?0+', parts[1]) is not None))
    return (set(), registers) if zero else (registers, set())


def live_vector_registers_at_exit(instructions, machine):
    """`[(index, [register numbers])]` for every exit some path reaches with a dirty register.

    Forward may-analysis over the function's own control-flow graph: a register is dirty at a
    join if it is dirty on any incoming edge, so a wipe on one arm of a branch does not cover the
    other, and a write in a loop body after the wipe is seen through the backedge. Exits are
    `ret` and tail jumps. Calls leave the set unchanged: each audited callee answers for its own
    registers, and a kernel must still wipe after its last use, not before a call.
    """
    arm = machine == 183
    tracked = (set(range(8)) | set(range(16, 32))) if arm else set(range(32))
    addresses = getattr(instructions, 'addresses', [])
    relocations = getattr(instructions, 'relocations', {})
    positions = {address: index for index, address in enumerate(addresses)}
    incoming = {}
    exits = {}
    pending = [(0, frozenset())]
    while pending:
        index, dirty = pending.pop()
        if index >= len(instructions):
            continue
        previous = incoming.get(index)
        if previous is not None:
            if dirty <= previous:
                continue
            dirty = dirty | previous
        incoming[index] = dirty
        mnemonic, operands = instructions[index]
        target_text = operands.split(',')[-1].strip()
        target = (positions.get(int(target_text, 16))
                  if re.fullmatch(r'(?:0x)?[0-9a-f]+', target_text) else None)
        if mnemonic in ('ret', 'retq') or (arm and mnemonic in ('br', 'braa', 'brab')):
            if dirty:
                exits[index] = dirty
            continue
        if mnemonic in ('jmp', 'jmpq', 'b'):
            if index in relocations or target is None:
                # Tail call, or a jump this decoder cannot follow: the registers leave with it.
                if dirty:
                    exits[index] = dirty
            else:
                pending.append((target, dirty))
            continue
        written, zeroed = vector_register_effect(mnemonic, operands, machine)
        dirty = frozenset((dirty - zeroed) | (written & tracked))
        if conditional(mnemonic) and target is not None:
            pending.append((target, dirty))
        pending.append((index + 1, dirty))
    return [(index, sorted(registers)) for index, registers in sorted(exits.items())]


def vector_wipe_errors(symbol, instructions, machine):
    if not is_simd_kernel_symbol(symbol):
        return []
    name = 'v{}' if machine == 183 else 'xmm{0}/ymm{0}/zmm{0}'
    return [f'{symbol}[{index}]: unzeroed live vector registers at exit: '
            f'{[name.format(register) for register in registers]}'
            for index, registers in live_vector_registers_at_exit(instructions, machine)]


def writes_vector_registers(instructions, machine):
    return any(vector_register_effect(mnemonic, operands, machine)[0]
               for mnemonic, operands in instructions)


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
        elif not mnem.startswith(("str", "stur", "stp", "st1", "st2", "st3", "st4")):
            if mnem.startswith(("ld1", "ld2", "ld3", "ld4")):
                for vn in expand_a64_neon_list(ops_l):
                    dirty_neon.add(vn)
            elif mnem == "ldp" and len(parts) >= 2:
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


def extract_elf_disasm_and_rodata_syms(
    archive_or_obj: Path, llvm_objdump: str | None = None
) -> tuple[str, list[str]]:
    disasm_chunks: list[str] = []
    symtab_lines: list[str] = []
    dis_cmd = (
        [llvm_objdump, "-dr", "-C", "--x86-asm-syntax=intel"]
        if llvm_objdump
        else ["objdump", "-dr", "-C", "-M", "intel"]
    )
    sym_tool = llvm_objdump or "objdump"
    if archive_or_obj.read_bytes()[:4] == b"\x7fELF":
        disasm_chunks.append(subprocess.check_output([*dis_cmd, str(archive_or_obj)], text=True))
        symtab_lines.extend(
            subprocess.check_output([sym_tool, "-t", str(archive_or_obj)], text=True).splitlines()
        )
    else:
        with tempfile.TemporaryDirectory() as tmpdir:
            subprocess.check_call(["ar", "x", str(archive_or_obj)], cwd=tmpdir)
            for member in sorted(Path(tmpdir).iterdir()):
                if member.is_file() and member.read_bytes()[:4] == b"\x7fELF":
                    disasm_chunks.append(
                        subprocess.check_output([*dis_cmd, str(member)], text=True)
                    )
                    symtab_lines.extend(
                        subprocess.check_output([sym_tool, "-t", str(member)], text=True).splitlines()
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
    out, symtab_lines = extract_elf_disasm_and_rodata_syms(rlib_path, args.llvm_objdump)
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
        e_out, _ = extract_elf_disasm_and_rodata_syms(ep, args.llvm_objdump)
        archives_to_scan.append((ep.name, parse_objdump_functions(e_out)))

    expected_x86_set = set(EXPECTED_X86_SYMBOLS) | set(EXPECTED_X86_BITSLICE_SYMBOLS)
    for arch_name, arch_funcs in archives_to_scan:
        for sym, ins in sorted(arch_funcs.items()):
            if sym in expected_x86_set or not is_rust_crypto_symbol(sym):
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
coverage: absent symbols are listed, never counted as audited. Destructors of the
`qsag_asm::wipe` secret guards are screened; other drop glue is not. This instruction
screen is not a proof of data-independent control flow. Rust protocol functions
can branch on public lengths/state; --strict-rust-branches checks their taint
under the documented entry ABI. Assembly kernels always use the existing taint-aware
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
RUST_MODULES = ('qsag_hd::linear_module::', 'qsag_asm::aarch64_simd::',
                'qsag_asm::linear_map::',
                'qsag_core::rss256::', 'qsag_core::wots_c::', 'qsag_quorum::dzk::',
                'qsag_asm::bitslice::', 'qsag_asm::portable::',
                'qsag_asm::avx512::', 'qsag_asm::gf256_simd::',
                'qsag_asm::sha2_hw::', 'qsag_asm::ntt_simd::')


# Required out-of-line SIMD entrypoints in the release qsag-asm archive. A
# namespace-only check could otherwise pass after one kernel disappeared.
REQUIRED_SIMD_SYMBOLS = {
    62: tuple('qsag_asm::' + name for name in (
        'avx512::keccak_f1600_avx512_8x', 'avx512::poly_scale_xor_avx512_evex',
        'avx512::gf2_128_mul_acc_avx512_evex', 'avx512::gf256_shamir_mac_avx512_gfni',
        'avx512::gf256_shamir_mul_avx512_gfni', 'avx512::tower128_bdoz_mac_avx512_evex',
        'gf256_simd::gf256_shamir_mul_vpshufb_avx2',
        'gf256_simd::gf256_shamir_mac_vpshufb_avx2_x1',
        'gf256_simd::gf256_shamir_mac_4vpshufb_avx2_x2',
        'linear_map::gfni128', 'linear_map::gfni512', 'linear_map::gfni512x8',
        'sha2_hw::sha256_compress_blocks_shani',
        'ntt_simd::x86_simd::mldsa_ntt_avx2', 'ntt_simd::x86_simd::mldsa_ntt_avx512',
        'ntt_simd::x86_simd::mldsa_inv_ntt_avx2', 'ntt_simd::x86_simd::mldsa_inv_ntt_avx512',
        'ntt_simd::x86_simd::mldsa_pointwise_mul_avx2',
        'ntt_simd::x86_simd::mldsa_pointwise_mul_avx512')),
    183: tuple('qsag_asm::' + name for name in (
        'aarch64_simd::gf256_shamir_mul_pmull_neon',
        'aarch64_simd::gf256_shamir_mac_pmull_neon',
        'aarch64_simd::keccak_chi_mpc_row256_neon',
        'aarch64_simd::mldsa_ntt_neon',
        'aarch64_simd::mldsa_inv_ntt_neon',
        'aarch64_simd::mldsa_pointwise_mul_neon',
        'linear_map::pmull_map',
        'sha2_hw::sha256_compress_blocks_aarch64_sha2')),
}


def missing_simd_symbols(audited, machine):
    return [symbol for symbol in REQUIRED_SIMD_SYMBOLS[machine] if symbol not in audited]


def is_rust_crypto_symbol(symbol):
    # Storage, CPU discovery, formatting and allocation are outside the kernel
    # ABI. Include root-level dispatch wrappers as well as nested SIMD modules.
    if is_rust_non_crypto_helper(symbol) or 'qsag_asm::durable::' in symbol:
        return False
    if re.search(r'::(?:tests|[A-Za-z0-9_]+_tests)::', symbol):
        return False
    return ('qsag_asm::' in symbol or any(module in symbol for module in RUST_MODULES)
            or 'gf2_128_mul_acc_batch' in symbol)


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


def rust_errors(symbol, instructions, strict=False, machine=None):
    """Instruction taint screen, with explicit public pointer/length ABI assumptions.

    Buffer contents are secret; pointer and length arguments are public. Scalar
    field primitives instead receive secret value arguments. Stack spills retain
    taint and vector/GPR transfers share one register domain. The intraprocedural CFG reaches a taint fixpoint at joins and backedges. It
    is not an interprocedural proof: callers must establish the entry contract.
    """
    if not instructions:
        return [f'{symbol}: empty instruction stream']
    if machine is None:
        machine = 183 if any(re.search(r'\b[wx][0-9]+\b', op) or m.startswith('b.')
                             or m in AARCH64_DIV_MNEMONICS | AARCH64_VAR_SHIFT_MNEMONICS
                             or m in ('cbz', 'cbnz', 'tbz', 'tbnz') for m, op in instructions) else 62
    arm = machine == 183
    def reg(token):
        token = re.sub(r'\[[0-9]+\]$', '', token.strip()).strip('{} ')
        if arm:
            return canon_a64_gpr(token) or canon_a64_neon(token)
        scalar = canon_x86_gpr(token)
        vector = canon_x86_simd(token)
        return scalar or (f'v{vector}' if vector is not None else None)
    def regs(op):
        return {r for t in re.findall(r'\b[a-z][a-z0-9]*(?:\.[0-9]*[bhsdq])?\b', op)
                if (r := reg(t)) is not None}
    def stack_key(mem):
        compact = mem.replace(' ', '').replace('#', '').replace(',', '+').replace('+-', '-')
        match = re.fullmatch(r'(rsp|rbp|sp|x29)([+-](?:0x[0-9a-f]+|[0-9]+))?', compact)
        if not match:
            return None
        displacement = match[2] or '+0'
        return match[1], int(displacement[1:], 0) * (-1 if displacement[0] == '-' else 1)
    def width(operand, mnemonic):
        if arm:
            if mnemonic.endswith('b'):
                return 1
            if mnemonic.endswith('h'):
                return 2
            return 16 if operand.startswith(('q', 'v')) else 4 if operand.startswith(('w', 's')) else 8
        for name, size in (('zmmword', 64), ('ymmword', 32), ('xmmword', 16),
                           ('qword', 8), ('dword', 4), ('word', 2), ('byte', 1)):
            if name in operand:
                return size
        return 64 if 'zmm' in operand else 32 if 'ymm' in operand else 16 if 'xmm' in operand else 8
    is_clmul64_acc = 'gf2_64x128_clmul_acc' in symbol or '::clmul_64x128_acc_' in symbol
    scalar = (not is_clmul64_acc) and (is_branchless_portable_primitive(symbol) or any(
        name in symbol for name in ('ct_reduce_mod_q_', '::mod_q_', 'goldilocks_',
                                     'wiedemann_', 'clmul', 'tower_mul', 'tower_scale')))
    taint = ({f'x{i}' for i in range(8)} if arm else
             {'rdi', 'rsi', 'rdx', 'rcx', 'r8', 'r9'}) if scalar else set()
    # The final backend argument is public, even when field operands are secret.
    if symbol.endswith('::goldilocks_mul_ct_with_backend'):
        taint.discard('x2' if arm else 'rdx')
    elif symbol.endswith('::goldilocks_pow7_ct_with_backend'):
        taint.discard('x1' if arm else 'rsi')
    taint.update(f'v{i}' for i in range(32))
    stack = {}
    if not arm and symbol.endswith('::gf256_shamir_mul_with_backend'):
        # Three slice descriptors occupy the six argument registers; backend is
        # the seventh SysV argument, a public byte at entry rsp + 8.
        stack['rsp', 8] = False
    if not arm and symbol.endswith('::gf2_128_scale_xor_with_backend'):
        # Seven-argument SysV signature: backend is the first stack argument;
        # the two scalar field limbs in r8/r9 are secret.
        taint.update(('r8', 'r9'))
        stack['rsp', 8] = False
    if 'gf2_64x128_clmul_acc' in symbol:
        # `(acc: &mut [[u128; 2]], words: &[u64], scalar: u128[, backend: SimdBackend])`:
        # `acc` and `words` are public slice descriptors (contents secret); `scalar` limbs are secret.
        taint.update(('x4', 'x5') if arm else ('r8', 'r9'))
        if not arm and symbol.endswith('_with_backend'):
            stack['rsp', 8] = False
    public_pointer = set()
    if any(name in symbol for name in ('::gf2_xor_combine_planes', '::xor_combine_planes_avx2')):
        # Documented `bitslice.rs` contract: `rows` (`rdi`/`x0`) is secret; `pattern` (`rsi`/`x1`)
        # is the public subset-XOR nibble selector matrix.
        public_pointer.add('x1' if arm else 'rsi')
    if re.search(r'drop_(?:in_place|glue)::<qsag_asm::wipe::SecretBuffer<alloc::vec::Vec<', symbol):
        # The guard is exactly a `Vec` header: capacity, pointer and length are public, and
        # freeing depends on the capacity. What the pointer leads to stays secret.
        public_pointer.add('x0' if arm else 'rdi')
    flags = True
    errors = []
    addresses = getattr(instructions, 'addresses', [])
    positions = {address: index for index, address in enumerate(addresses)}
    incoming = {}
    pending = [(0, taint, stack, public_pointer, flags)]
    visits = 0
    while pending:
        visits += 1
        if visits > 128 * len(instructions):
            return [f"{symbol}: dataflow did not converge within the analysis budget"]
        i, taint, stack, public_pointer, flags = pending.pop()
        if i >= len(instructions):
            continue
        previous = incoming.get(i)
        if previous is not None:
            old_taint, old_stack, old_public, old_flags = previous
            taint = taint | old_taint
            # The map holds public slots only (see `store_stack`); a slot is public after a
            # join exactly when it is public on both edges.
            stack = {key: False for key in stack.keys() & old_stack.keys()}
            public_pointer = public_pointer & old_public
            flags |= old_flags
            if (taint, stack, public_pointer, flags) == previous:
                continue
        incoming[i] = (taint.copy(), stack.copy(), public_pointer.copy(), flags)
        mnemonic, operands = instructions[i]
        successors = [i + 1]
        if positions:
            target_text = operands.split(',')[-1].strip()
            target = int(target_text, 16) if re.fullmatch(r'(?:0x)?[0-9a-f]+', target_text) else None
            if conditional(mnemonic):
                if target in positions:
                    successors.append(positions[target])
                else:
                    errors.append(f'{symbol}[{i}]: unresolved conditional target')
            elif mnemonic in ('jmp', 'jmpq', 'b'):
                reloc_jmp = getattr(instructions, 'relocations', {}).get(i, '')
                successors = [positions[target]] if (not reloc_jmp and target in positions) else []
            elif mnemonic in ('ret', 'retq'):
                successors = []
        # Preserve spill identities when the stack pointer moves. Unknown stack
        # adjustments invalidate the map rather than declaring new contents public.
        stack_base = 'sp' if arm else 'rsp'
        delta = None
        if not arm and mnemonic in ('push', 'pop'):
            delta = -8 if mnemonic == 'push' else 8
        elif mnemonic in ('add', 'sub') and operands.split(',')[0].strip() == stack_base:
            amount = operands.split(',')[-1].strip().lstrip('#')
            if re.fullmatch(r'(?:0x[0-9a-f]+|[0-9]+)', amount):
                delta = int(amount, 0) * (-1 if mnemonic == 'sub' else 1)
            else:
                stack = {key: value for key, value in stack.items() if key[0] != stack_base}
        if delta is not None:
            stack = {(base, offset - delta if base == stack_base else offset): value
                     for (base, offset), value in stack.items()}
        try:
            if mnemonic in ('nop', 'nopl', 'nopw', 'endbr64') or (
                    mnemonic == 'data16' and 'nop' in operands.lower()):
                continue
            op = operands.lower()
            parts = [p.strip() for p in re.split(r',\s*(?![^\[]*\])', op)] if op else []
            relocation = getattr(instructions, 'relocations', {}).get(i, '')
            public_symbol = any(n in relocation for n in (
                'qsag_asm::cpuid::CACHED_', 'qsag_asm::cpuid::BACKEND', '.LCPI', '.rodata.',
                'T7_TO_POLY_SELECTORS', 'NTT_TABLES', 'T3_VPSHUFB_CONSTS',
                'SHA256_HW_CONSTS', 'AVX2_GF256_ISO_LUTS', 'AARCH64_GF256_PMULL_CONSTS',
                'ByteMatrices'))
            size = width(op if not arm else (parts[0] if parts else ''), mnemonic)
            def store_stack(mem, value, length=size, extra=0):
                # Normal form: a slot that is not recorded reads as secret, so secret
                # stores remove the slot instead of recording it. This keeps the state
                # finite when a stack-probe loop moves the stack pointer on its backedge.
                key = stack_key(mem)
                if key:
                    base, offset = key
                    for byte in range(length):
                        if value:
                            stack.pop((base, offset + extra + byte), None)
                        else:
                            stack[base, offset + extra + byte] = False
            def secret(value):
                memory = re.findall(r'(?<![a-z0-9.])\[([^\]]+)\]', value)
                if memory:
                    def loaded(mem):
                        key = stack_key(mem)
                        if key:
                            base, offset = key
                            return any(stack.get((base, offset + byte), True) for byte in range(size))
                        mem_regs = regs(mem)
                        is_pub_deref = bool(mem_regs & public_pointer) and not (mem_regs & taint)
                        return not (public_symbol or is_pub_deref)
                    return any(loaded(mem) for mem in memory)
                return bool(regs(value) & taint)
            def fail(reason):
                errors.append(f'{symbol}[{i}]: {reason} `{mnemonic} {operands}`')
            if mnemonic in X86_DIV_MNEMONICS | AARCH64_DIV_MNEMONICS or mnemonic.startswith(('fdiv', 'vdiv')):
                fail('forbidden divider')
            if mnemonic in X86_GATHER_MNEMONICS:
                fail('gather requires an address contract')
            for mem in re.findall(r'(?<![a-z0-9.])\[([^\]]+)\]', op):
                if mnemonic != 'lea' and regs(mem) & taint:
                    fail('secret-tainted memory address')
            branch_secret = flags
            if mnemonic in ('cbz', 'cbnz', 'tbz', 'tbnz', 'jrcxz', 'jecxz'):
                branch_secret = secret(parts[0]) if parts else True
            if conditional(mnemonic) and (strict or scalar) and branch_secret:
                fail('secret-tainted conditional branch')
            selection_sources = parts[1:] if arm else parts
            if (mnemonic.startswith('cmov') or mnemonic in AARCH64_CSEL_MNEMONICS) and (
                    flags or any(secret(p) for p in selection_sources)):
                fail('secret-tainted conditional selection')
            variable = (mnemonic in X86_BMI2_VAR_SHIFT_MNEMONICS | AARCH64_VAR_SHIFT_MNEMONICS or
                        mnemonic in X86_SHIFT_MNEMONICS | {'lsl', 'lsr', 'asr', 'ror'})
            if variable and len(parts) >= 2 and secret(parts[-1]):
                fail('secret-tainted variable shift')
            if mnemonic in ('cmp', 'test', 'bt', 'tst', 'cmn', 'ucomisd', 'comisd'):
                flags = any(secret(p) for p in parts)
                continue
            if not arm and mnemonic in ('mul', 'imul') and len(parts) == 1:
                value = secret(parts[0]) or 'rax' in taint
                for destination in ('rax', 'rdx'):
                    if value:
                        taint.add(destination)
                    else:
                        taint.discard(destination)
                flags = value
                continue
            if not arm and mnemonic == 'push' and parts:
                store_stack('rsp', secret(parts[0]), 8)
                continue
            if not arm and mnemonic == 'pop' and parts:
                destination = reg(parts[0])
                if destination:
                    if any(stack.get(('rsp', byte - 8), True) for byte in range(8)):
                        taint.add(destination)
                    else:
                        taint.discard(destination)
                continue
            if not parts or conditional(mnemonic) or mnemonic in ('ret', 'jmp', 'b', 'nop', 'push'):
                continue
            if mnemonic in ('call', 'callq', 'bl', 'blr'):
                if any(p in relocation for p in ('panicking::', 'assert_failed', 'panic_bounds_check',
                                                 'slice_end_index_len_fail', 'slice_start_index_len_fail')):
                    successors = []
                    continue
                if 'qsag_asm::cpuid::probe_capabilities' in relocation:
                    # The concrete Rust return ABI writes seventeen public capability bytes
                    # through rdi (SysV) or x8 (AAPCS indirect result), or u32 bits in eax/w0.
                    if 'probe_capabilities_bits' not in relocation:
                        target = 'x8' if arm else 'rdi'
                        for j in range(i - 1, -1, -1):
                            m, operand = instructions[j]
                            operands_j = [p.strip().lower() for p in operand.split(',')]
                            if not operands_j or reg(operands_j[0]) != target:
                                continue
                            if m == 'mov' and len(operands_j) == 2 and reg(operands_j[1]):
                                if operands_j[1] in ('sp', 'rsp', 'x29', 'rbp'):
                                    store_stack(operands_j[1], False, 17)
                                    break
                                target = reg(operands_j[1])
                                continue
                            if m == 'lea':
                                for mem in re.findall(r'\[([^\]]+)\]', operand.lower()):
                                    store_stack(mem, False, 17)
                            elif arm and m in ('add', 'sub') and len(operands_j) == 3:
                                displacement = operands_j[2].lstrip('#')
                                store_stack(operands_j[1] + ('-' if m == 'sub' else '+') + displacement, False, 17)
                            break
                    taint.difference_update(('x0', 'x1') if arm else ('rax', 'rdx'))
                    continue
                # Unknown return values must not become public by accident.
                taint.update(('x0', 'x1') if arm else ('rax', 'rdx'))
                flags = True
                continue
            if arm and mnemonic.startswith(('str', 'stur', 'stp', 'st1')):
                for mem in re.findall(r'(?<![a-z0-9.])\[([^\]]+)\]', op):
                    store_stack(mem, secret(parts[0]))
                    if mnemonic == 'stp':
                        store_stack(mem, secret(parts[1]), extra=size)
                continue
            dst = reg(parts[0])
            sources = parts[2:] if arm and mnemonic == 'ldp' else parts[1:]
            move = mnemonic.startswith(('mov', 'vmov', 'ldr', 'ldur', 'ldp', 'fmov', 'umov', 'smov'))
            if mnemonic == 'lea':
                value = bool(regs(','.join(sources)) & taint)
            else:
                value = any(secret(p) for p in sources)
                if not arm and not move and not mnemonic.startswith('v') and not (
                        mnemonic == 'imul' and len(parts) == 3):
                    value |= secret(parts[0])
            zero = (mnemonic in ('xor', 'sub', 'pxor', 'xorps', 'xorpd') and len(parts) == 2 and parts[0] == parts[1]) or (
                mnemonic in ('vpxor', 'vpxorq', 'vpxord', 'vxorps', 'vxorpd', 'eor', 'sub') and len(parts) == 3 and parts[1] == parts[2])
            if arm and mnemonic in ('ins', 'bfi', 'bfxil', 'sli', 'sri', 'bsl', 'bit', 'bif'):
                value |= secret(parts[0])
            if zero:
                value = False
            if not arm and dst and canon_x86_gpr(parts[0]) and not (
                    parts[0] == dst or parts[0].startswith('e') or re.fullmatch(r'r[0-9]+d', parts[0])):
                # Byte/word writes preserve higher bits of the enclosing GPR.
                value |= dst in taint
            if (mnemonic.startswith(('cmov', 'set')) or mnemonic in AARCH64_CSEL_MNEMONICS
                    or mnemonic in ('adc', 'adcs', 'sbb', 'sbc', 'sbcs')):
                value |= flags
            if dst:
                is_public_pointer = (
                    public_symbol
                    or (move and sources and reg(sources[0]) in public_pointer)
                    or (not arm and not value and dst in public_pointer
                        and mnemonic in ('add', 'sub', 'inc', 'dec'))
                    # AArch64 arithmetic has a separate source and destination. Preserve
                    # public-buffer provenance only from its base, with a public offset.
                    or (arm and not value and mnemonic in ('add', 'sub')
                        and sources and reg(sources[0]) in public_pointer)
                    or (mnemonic == 'lea' and not value and bool(regs(','.join(sources)) & public_pointer))
                )
                public_pointer.discard(dst)
                if is_public_pointer:
                    public_pointer.add(dst)
                if value:
                    taint.add(dst)
                else:
                    taint.discard(dst)
            if arm and mnemonic.startswith(('ld1', 'ld2', 'ld3', 'ld4')) and '{' in op:
                mem_sources = [p for p in parts if '[' in p]
                list_secret = any(secret(p) for p in mem_sources) if mem_sources else True
                for vn in expand_a64_neon_list(op):
                    public_pointer.discard(vn)
                    if list_secret:
                        taint.add(vn)
                    else:
                        taint.discard(vn)
            elif arm and mnemonic == 'ldp' and len(parts) > 1:
                second = reg(parts[1])
                mem = re.search(r'\[([^\]]+)\]', op)
                key = stack_key(mem[1]) if mem else None
                second_value = any(stack.get((key[0], key[1] + size + byte), True)
                                   for byte in range(size)) if key else value
                if second_value:
                    taint.add(second)
                else:
                    taint.discard(second)
            elif '[' in parts[0]:
                for mem in re.findall(r'\[([^\]]+)\]', parts[0]):
                    store_stack(mem, value)
            if not arm and mnemonic in ('rol', 'ror', 'rcl', 'rcr', 'inc', 'dec'):
                flags |= value
            if (not arm and mnemonic in ('add', 'sub', 'and', 'or', 'xor', 'adc', 'sbb', 'inc', 'dec',
                            'neg', 'shl', 'shr', 'sar')) or (arm and mnemonic in ('adds', 'subs', 'ands', 'adcs', 'sbcs')):
                flags = value
        finally:
            for successor in successors:
                pending.append((successor, taint.copy(), stack.copy(), public_pointer.copy(), flags))
    return sorted(set(errors))


def vector_wipe_self_tests():
    """#tooth: every way a compiled SIMD kernel can leave a vector register must be rejected."""
    def stream(operations):
        out = InstructionStream()
        out.extend(operations)
        out.addresses = list(range(0, 4 * len(out), 4))
        return out
    x86 = 'qsag_asm::linear_map::gfni512x8'
    arm = 'qsag_asm::linear_map::pmull_map'
    xmm_wipe = [('pxor', f'xmm{i}, xmm{i}') for i in range(16)]
    zmm_wipe = [('vpxorq', f'zmm{i}, zmm{i}, zmm{i}') for i in range(32)] + [('vzeroupper', '')]
    neon_wipe = [('eor', f'v{i}.16b, v{i}.16b, v{i}.16b') for i in list(range(8)) + list(range(16, 32))]
    load = [('vmovdqu64', 'zmm3, zmmword ptr [rsi]')]
    rejected = [
        # No wipe at all; `vzeroupper` alone; `vzeroall` does not reach zmm16..zmm31.
        (x86, 62, [('movdqu', 'xmm3, xmmword ptr [rsi]'), ('ret', '')]),
        (x86, 62, load + [('vzeroupper', ''), ('ret', '')]),
        (x86, 62, [('vmovdqu64', 'zmm17, zmmword ptr [rsi]'), ('vzeroall', ''), ('ret', '')]),
        # A wipe that skips one register; a reload after the wipe; a masked self-XOR.
        (x86, 62, load + [w for w in zmm_wipe if not w[1].startswith('zmm3,')] + [('ret', '')]),
        (x86, 62, zmm_wipe + [('movq', 'xmm0, rax'), ('ret', '')]),
        (x86, 62, load + [('vpxorq', 'zmm3 {k1}, zmm3, zmm3'), ('vzeroupper', ''), ('ret', '')]),
        # The wipe sits on one arm of a branch only (index 2 jumps past it to the `ret`).
        (x86, 62, stream(load + [('test', 'rdx, rdx'), ('je', '0x14'),
                                 ('vpxorq', 'zmm3, zmm3, zmm3'), ('vzeroupper', ''), ('ret', '')])),
        # A loop body dirties the register again after the wipe at its head.
        (x86, 62, stream([('pxor', 'xmm3, xmm3'), ('movdqu', 'xmm3, xmmword ptr [rsi]'),
                          ('dec', 'rcx'), ('jne', '0x0'), ('ret', '')])),
        # A tail call leaves with the registers.
        (x86, 62, stream(load + [('jmp', 'rax')])),
        (arm, 183, [('ldr', 'q24, [x1]'), ('ret', '')]),
        (arm, 183, [('ld1', '{ v28.16b - v31.16b }, [x0]')] + neon_wipe[:-1] + [('ret', '')]),
        (arm, 183, [('ldp', 'q0, q17, [x8]'), ('eor', 'v0.16b, v0.16b, v0.16b'), ('ret', '')]),
        (arm, 183, [('pmull', 'v16.1q, v0.1d, v2.1d')] + neon_wipe + [('fmov', 'd0, x1'), ('ret', '')]),
        # A half-width XOR is not a wipe.
        (arm, 183, [('ldr', 'q5, [x1]'), ('eor', 'v5.8b, v5.8b, v5.8b'), ('ret', '')]),
        (arm, 183, stream([('ldr', 'q5, [x1]'), ('cbz', 'x2, 0xc'),
                           ('eor', 'v5.16b, v5.16b, v5.16b'), ('ret', '')])),
    ]
    for symbol, machine, operations in rejected:
        assert vector_wipe_errors(symbol, operations, machine), (symbol, list(operations))
    accepted = [
        (x86, 62, [('movdqu', 'xmm3, xmmword ptr [rsi]'), ('movq', 'rax, xmm3')] + xmm_wipe + [('ret', '')]),
        (x86, 62, load + [('vmovdqu64', 'zmm17, zmmword ptr [rsi]')] + zmm_wipe + [('ret', '')]),
        (x86, 62, load + [('vzeroall', ''), ('ret', '')]),
        # The wipe runs before the join that both arms reach.
        (x86, 62, stream(load + [('vpxorq', 'zmm3, zmm3, zmm3'), ('vzeroupper', ''),
                                 ('test', 'rdx, rdx'), ('je', '0x18'), ('mov', 'rax, rdx'), ('ret', '')])),
        (arm, 183, [('ld1', '{ v28.16b - v31.16b }, [x0]'), ('pmull', 'v16.1q, v0.1d, v2.1d')]
         + neon_wipe + [('ret', '')]),
        # Callee-saved v8..v15 are restored by the epilogue, and an all-zero `movi` is a wipe.
        (arm, 183, [('ldr', 'q5, [x1]'), ('movi', 'v5.2d, #0000000000000000'),
                    ('ldp', 'd9, d8, [sp]'), ('ret', '')]),
    ]
    for symbol, machine, operations in accepted:
        assert not vector_wipe_errors(symbol, operations, machine), (symbol, list(operations))
    # The check is tied to the kernel set, and the set covers every required SIMD entrypoint.
    assert not vector_wipe_errors('qsag_asm::portable::clmul64_portable',
                                  [('movdqu', 'xmm3, xmmword ptr [rsi]'), ('ret', '')], 62)
    for names in REQUIRED_SIMD_SYMBOLS.values():
        assert all(is_simd_kernel_symbol(name) for name in names)
    return len(rejected) + len(accepted) + 2


def self_tests():
    count = kernel_audit.run_negative_self_tests()
    dirty_call = [('vpxor', 'ymm0,ymm0,ymm0'), ('call', 'callee'), ('ret', '')]
    assert audit_compiled_rust_x86_symbol('probe', dirty_call)
    clean_call = dirty_call[:1] + [('vzeroupper', '')] + dirty_call[1:]
    assert not audit_compiled_rust_x86_symbol('probe', clean_call)
    dirty_zmm = [('vpxorq', 'zmm0, zmm0, zmm0'), ('ret', '')]
    assert audit_compiled_rust_x86_symbol('probe_zmm', dirty_zmm)
    clean_zmm = [('vpxorq', 'zmm0, zmm0, zmm0'), ('vzeroupper', ''), ('ret', '')]
    assert not audit_compiled_rust_x86_symbol('probe_zmm', clean_zmm)
    assert not audit_x86_symbol('avx512_zero', [('vpxorq', 'zmm16, zmm16, zmm16'), ('vzeroupper', ''), ('ret', '')])
    assert audit_aarch64_symbol('neon_ld4_leak', [('ld4', '{ v24.16b, v25.16b, v26.16b, v27.16b }, [x0]'),
                                                  ('eor', 'v24.16b, v24.16b, v24.16b'), ('ret', '')])
    assert audit_aarch64_symbol('neon_ld1_range_leak', [('ld1', '{ v28.16b - v31.16b }, [x0]'), ('ret', '')])
    assert audit_compiled_rust_aarch64_symbol('qsag_asm::aarch64_simd::mldsa_ntt_neon',
                                              [('eor', 'v23.16b, v23.16b, v23.16b'),
                                               ('add', 'v24.4s, v24.4s, v24.4s'), ('ret', '')], True)
    assert not audit_compiled_rust_aarch64_symbol('qsag_asm::aarch64_simd::mldsa_ntt_neon',
                                                  [('add', 'v24.4s, v24.4s, v24.4s'),
                                                   ('eor', 'v24.16b, v24.16b, v24.16b'), ('ret', '')], True)
    count += 9
    count += vector_wipe_self_tests()
    for mnemonic in ('div', 'idiv', 'udiv', 'sdiv', 'fdiv', 'jne', 'b.eq', 'cbz', 'cbnz', 'tbz', 'tbnz'):
        assert rust_errors('qsag_hd::linear_module::ct_reduce_mod_q_u64', [(mnemonic, '')])
        count += 1
    for kind in (1, 2, 3):
        for machine in BITSLICE:
            data = b'\x7fELF\x02\x01' + bytes(10) + kind.to_bytes(2, 'little') + machine.to_bytes(2, 'little')
            assert elf_header(data) == (kind, machine)
            count += 1
    for mnemonic, operands in [('cmovne', 'rax, rbx'), ('shl', 'rax, cl'),
                               ('shlx', 'rax, rbx, rcx'), ('lslv', 'x0, x1, x2')]:
        assert rust_errors('qsag_asm::portable::clmul_probe', [(mnemonic, operands)])
        count += 1
    # Scalar secret -> vector -> scalar -> address must not launder taint.
    bridge = [('movq', 'xmm0, rdi'), ('movq', 'rax, xmm0'),
              ('mov', 'rdx, [rax]'), ('pxor', 'xmm0, xmm0'), ('ret', '')]
    assert any('secret-tainted' in e for e in audit_x86_symbol('goldilocks_bridge', bridge))
    # Wiping a vector before exporting it to a scalar removes that dependency.
    wiped = [('movq', 'xmm0, rdi'), ('pxor', 'xmm0, xmm0'),
             ('movq', 'rax, xmm0'), ('mov', 'rbx, [rax]'), ('ret', '')]
    assert not audit_x86_symbol('goldilocks_bridge', wiped)
    count += 2
    # Each mutation starts from secret buffer data, not an assumed secret flag.
    for register in ('rax', 'rbx', 'r8', 'r9', 'r10', 'r11'):
        prefix = [('movdqu', 'xmm3, [rsi]'), ('movq', f'{register}, xmm3')]
        mutations = [
            [('test', f'{register}, {register}'), ('jne', '0x40')],
            [('cmp', f'{register}, 0'), ('cmovne', 'r12, r13')],
            [('mov', f'rcx, {register}'), ('shl', 'r12, cl')],
            [('mov', f'r12, [rdi + {register}*8]')],
        ]
        for suffix in mutations:
            assert rust_errors('buffer_probe', prefix + suffix, True, 62), (register, suffix)
            count += 1
    for register in ('x4', 'x5', 'x6', 'x7', 'x9', 'x10'):
        prefix = [('ldr', 'q3, [x1]'), ('umov', f'{register}, v3.d[0]')]
        mutations = [
            [('cbnz', f'{register}, 0x40')],
            [('cmp', f'{register}, #0'), ('csel', 'x12, x13, x14, ne')],
            [('lslv', f'x12, x13, {register}')],
            [('ldr', f'x12, [x0, {register}]')],
        ]
        for suffix in mutations:
            assert rust_errors('buffer_probe', prefix + suffix, True, 183), (register, suffix)
            count += 1
    for machine, clean in ((62, [('cmp', 'rsi, rdx'), ('jb', '0x40'),
                                 ('mov', 'rax, [rdi]'), ('sub', 'rcx, 1'), ('jne', '0x20')]),
                           (183, [('cmp', 'x1, x2'), ('b.lo', '0x40'),
                                  ('ldr', 'x4, [x0]'), ('subs', 'x3, x3, #1'), ('b.ne', '0x20')])):
        assert not rust_errors('buffer_probe', clean, True, machine)
        count += 1
    # Join/backedge regressions: a textual sweep would incorrectly accept these.
    for operations in (
        [('mov', 'eax, [rsi]'), ('test', 'edx, edx'), ('je', '0x10'),
         ('xor', 'eax, eax'), ('test', 'eax, eax'), ('jne', '0x18'), ('ret', '')],
        [('mov', 'ecx, 2'), ('xor', 'eax, eax'), ('test', 'eax, eax'), ('jne', '0x1c'),
         ('mov', 'eax, [rsi]'), ('dec', 'ecx'), ('jne', '0x8'), ('ret', '')],
    ):
        stream = InstructionStream()
        stream.extend(operations)
        stream.addresses = list(range(0, 4 * len(stream), 4))
        assert rust_errors('buffer_probe', stream, True, 62)
        count += 1
    # A stack-probe loop moves the stack pointer on its backedge. The analysis must reach a
    # fixpoint there, keep a public spill made after it, and forget one made before it.
    def probe(spill_before):
        operations = ([('mov', 'qword ptr [rsp + 0x8], rcx')] if spill_before else []) + [
            ('mov', 'r11, rsp'), ('sub', 'r11, 0xc000'),
            ('sub', 'rsp, 0x1000'), ('mov', 'qword ptr [rsp], 0x0'), ('cmp', 'rsp, r11'),
            ('jne', hex(8 + 4 * spill_before)), ('sub', 'rsp, 0x808')]
        operations += ([] if spill_before else [('mov', 'qword ptr [rsp + 0x8], rcx')]) + [
            ('mov', 'rax, qword ptr [rsp + 0x8]'), ('test', 'rax, rax'), ('je', '0x0'), ('ret', '')]
        out = InstructionStream()
        out.extend(operations)
        out.addresses = list(range(0, 4 * len(out), 4))
        return out
    assert not rust_errors('buffer_probe', probe(False), True, 62)
    assert any('secret-tainted conditional branch' in e
               for e in rust_errors('buffer_probe', probe(True), True, 62))
    count += 2
    partial_spill = [('mov', 'qword ptr [rsp], rdi'), ('mov', 'dl, [rsi]'),
                     ('mov', 'byte ptr [rsp+7], dl'), ('mov', 'rax, qword ptr [rsp]'),
                     ('test', 'rax, rax'), ('jne', '0x40')]
    assert rust_errors('buffer_probe', partial_spill, True, 62)
    count += 1
    paired_spill = [('ldr', 'x4, [x0]'), ('stp', 'x4, x1, [sp]'),
                    ('ldp', 'x5, x3, [sp]'), ('subs', 'x3, x3, #1'), ('b.ne', '0x40')]
    assert not rust_errors('buffer_probe', paired_spill, True, 183)
    count += 1
    for partial in ('al', 'ah', 'ax'):
        stream = [('mov', 'rax, [rsi]'), ('mov', f'{partial}, 0'),
                  ('test', 'rax, rax'), ('jne', '0x40')]
        assert rust_errors('buffer_probe', stream, True, 62)
        count += 1
    assert rust_errors('buffer_probe', [('mov', 'rax, [rsi]'), ('push', 'rax'),
                       ('pop', 'rcx'), ('shl', 'rdx, cl')], True, 62)
    count += 1
    for instruction in ('adc', 'sbb'):
        stream = [('mov', 'rax, [rsi]'), ('cmp', 'rax, 0'), ('mov', 'ecx, 0'),
                  (instruction, 'ecx, 0'), ('mov', 'rax, [rdi+rcx]')]
        assert rust_errors('buffer_probe', stream, True, 62)
        count += 1
    # #tooth: `gf2_64x128_clmul_acc` must reject branches/addresses on secret `scalar` (`r8`/`r9`)
    # or secret `words` (`[rdx]`), while permitting public slice length loop on `rsi`/`rcx`.
    assert rust_errors('qsag_asm::bitslice::gf2_64x128_clmul_acc_portable',
                       [('test', 'r8, r8'), ('jne', '0x20')], True, 62)
    assert rust_errors('qsag_asm::bitslice::gf2_64x128_clmul_acc_portable',
                       [('mov', 'rax, [rdx]'), ('mov', 'rbx, [rdi + rax*8]')], True, 62)
    # #tooth: `gf2_xor_combine_planes` must still reject branches/addresses on secret `rows` (`[rdi]`)
    # or secret-offset indexing into `pattern` (`rsi + secret`), while permitting public offsets.
    assert rust_errors('qsag_asm::bitslice::gf2_xor_combine_planes_portable',
                       [('mov', 'rax, [rdi]'), ('mov', 'rbx, [rdx + rax*8]')], True, 62)
    assert rust_errors('qsag_asm::bitslice::gf2_xor_combine_planes_portable',
                       [('mov', 'rax, [rdi]'), ('lea', 'r10, [rsi + rax]'), ('movzx', 'ebx, byte ptr [r10]')], True, 62)
    assert not rust_errors('qsag_asm::bitslice::gf2_xor_combine_planes_portable',
                           [('add', 'rsi, 16'), ('movzx', 'eax, byte ptr [rsi]'),
                            ('and', 'eax, 15'), ('mov', 'rbx, [rdx + rax*8]')], True, 62)
    count += 5
    # Three-operand IMUL overwrites its destination; two-operand IMUL reads it.
    prefix = [('mov', 'rax, [rdi]')]
    sink = [('mov', 'r8, [rsi + rax]')]
    assert not rust_errors('buffer_probe', prefix + [('imul', 'rax, rcx, 200')] + sink, True, 62)
    assert rust_errors('buffer_probe', prefix + [('imul', 'rax, rcx')] + sink, True, 62)
    assert rust_errors('buffer_probe', prefix + [('imul', 'r8, rax, 200'),
        ('mov', 'r9, [rsi + r8]')], True, 62)
    assert is_rust_crypto_symbol('qsag_asm::keccak_f1600_batch_with_backend')
    # Guard destructors are screened; other drop glue is storage management.
    vec_guard = 'core::ptr::drop_glue::<qsag_asm::wipe::SecretBuffer<alloc::vec::Vec<u8>>>'
    array_guard = 'core::ptr::drop_glue::<qsag_asm::wipe::SecretBuffer<[u8; 32]>>'
    assert is_rust_crypto_symbol(vec_guard) and is_rust_crypto_symbol(array_guard)
    assert not is_rust_crypto_symbol('core::ptr::drop_glue::<qsag_asm::durable::LockedRecord>')
    capacity_branch = [('mov', 'rbx, rdi'), ('mov', 'rsi, qword ptr [rbx]'),
                       ('test', 'rsi, rsi'), ('je', '0x40')]
    content_branch = [('mov', 'r14, qword ptr [rdi + 0x8]'), ('mov', 'al, byte ptr [r14]'),
                      ('test', 'al, al'), ('je', '0x40')]
    # A `Vec` guard may branch on its capacity, never on what it holds; an inline guard
    # has no public header at all.
    assert not rust_errors(vec_guard, capacity_branch, True, 62)
    assert rust_errors(vec_guard, content_branch, True, 62)
    assert rust_errors(array_guard, capacity_branch, True, 62)
    count += 4
    assert not is_rust_crypto_symbol('<qsag_asm::durable::LockedRecord>::replace')
    assert not is_rust_crypto_symbol('<alloc::vec::Vec<u8>>::resize')
    # AArch64 CSEL overwrites its destination; a secret old destination is not
    # an operand. Secret condition flags and source registers remain rejected.
    assert not rust_errors('buffer_probe', [('ldr', 'x3, [x0]'), ('cmp', 'x1, x2'),
        ('csel', 'x3, x1, x2, lo')], True, 183)
    assert rust_errors('buffer_probe', [('ldr', 'x3, [x0]'), ('cmp', 'x3, x2'),
        ('csel', 'x4, x1, x2, lo')], True, 183)
    assert rust_errors('buffer_probe', [('ldr', 'x3, [x0]'), ('cmp', 'x1, x2'),
        ('csel', 'x4, x3, x2, lo')], True, 183)
    for machine, names in REQUIRED_SIMD_SYMBOLS.items():
        assert not missing_simd_symbols(names, machine)
        assert missing_simd_symbols(names[1:], machine) == [names[0]]
        count += 2
    count += 9
    pattern_symbol = 'qsag_asm::bitslice::gf2_xor_combine_planes_portable'
    # A public selector pointer copied to a new AArch64 register remains public.
    for arithmetic in ('add', 'sub'):
        prefix = [('mov', 'x20, x1'), (arithmetic, 'x6, x20, #7')]
        lookup = [('ldurb', 'w21, [x6, #-7]'), ('and', 'x21, x21, #15'),
                  ('add', 'x22, x2, x21, lsl #5'), ('ldp', 'q0, q1, [x22]')]
        assert not rust_errors(pattern_symbol, prefix + lookup, True, 183)
        # Secret row contents used as an offset must still be rejected.
        assert rust_errors(pattern_symbol, [('ldr', 'x7, [x0]'),
            (arithmetic, 'x6, x1, x7')] + lookup, True, 183)
        # A destination's old public provenance cannot bless a different base.
        assert rust_errors(pattern_symbol, [('mov', 'x6, x1'),
            (arithmetic, 'x6, x0, #7')] + lookup, True, 183)
        count += 3
    return count


def audit(path, objdump, strict, require_bitslice, require_namespaces=(), require_simd=False):
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
    executable = objdump or shutil.which('llvm-objdump')
    if not executable and shutil.which('rustc'):
        # rustup's llvm-tools component supplies a matching cross-architecture decoder.
        sysroot = Path(subprocess.check_output(['rustc', '--print', 'sysroot'], text=True).strip())
        candidates = sorted((sysroot / 'lib/rustlib').glob('*/bin/llvm-objdump'))
        if candidates:
            executable = str(candidates[0])
    executable = executable or ('objdump' if machine == 62 else 'aarch64-linux-gnu-objdump')
    command = [executable, '-dr', '-C']
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
    wiped_kernels, unenforced_vector_writers = [], []
    for symbol, instructions in functions.items():
        # Test/benchmark timing and assertion code is not a cryptographic kernel.
        if re.search(r'::(?:tests|[A-Za-z0-9_]+_tests)::', symbol):
            continue
        base = symbol.lstrip('_')
        if base in expected or base.startswith('qsag_bitslice_'):
            check = kernel_audit.audit_x86_symbol if machine == 62 else kernel_audit.audit_aarch64_symbol
            errors.extend(check(symbol, instructions))
        elif is_rust_crypto_symbol(symbol):
            if machine == 62:
                errors.extend(kernel_audit.audit_compiled_rust_x86_symbol(symbol, instructions, strict))
            else:
                errors.extend(kernel_audit.audit_compiled_rust_aarch64_symbol(symbol, instructions, strict))
            branches += sum(conditional(m) for m, _ in instructions)
            if is_simd_kernel_symbol(symbol):
                wiped_kernels.append(symbol)
            elif writes_vector_registers(instructions, machine):
                unenforced_vector_writers.append(symbol)
        else:
            continue
        audited.append(symbol)
    missing = [s for s in expected if not functions.get(s)]
    if require_bitslice:
        errors.extend(f'missing required bitslice kernel: {s}' for s in BITSLICE[machine] if s in missing)
    if kind in (2, 3):
        errors.extend(f'missing required linked assembly kernel: {symbol}' for symbol in missing)
    for module in require_namespaces:
        if not any(module in symbol for symbol in audited):
            errors.append(f'missing required Rust namespace: {module}')
    if require_simd:
        errors.extend(f'missing required SIMD kernel: {symbol}'
                      for symbol in missing_simd_symbols(audited, machine))
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
    print(f'  vector-register wipe at exit enforced on {len(wiped_kernels)} compiled SIMD kernels; '
          f'{len(unenforced_vector_writers)} other compiled functions write vector registers '
          'without that check (compiler-vectorized portable code)')
    for error in errors:
        print(f'  FAIL: {error}', file=sys.stderr)
    present = sum(any(module in symbol for symbol in audited) for module in RUST_MODULES)
    print(f'  instruction screen: {"FAIL" if errors else "PASS"} ({present}/{len(RUST_MODULES)} Rust namespaces present)')
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


def check_fixtures(fixture, x86_rlib, aarch64_rlib, binding="object", generation="current"):
    """Bind the literal certified archive, its SHA-256, and a fresh source build.

    Two bindings are available. `object` (the default) requires the fresh ELF member to be
    byte-identical to the certified one; it fails on any source, toolchain, flag or build-path
    drift, including drift in compiled Rust code that no certificate covers. `kernel-bytes`
    requires the same set of `qsag_asm_*` function symbols with identical code bytes, which is
    exactly what the Lean certificates quantify over and does not depend on the build path.
    Under either binding the embedded literal must hash to its recorded digest, so editing a
    digest alone cannot bless stale bytes, and every differing symbol is reported by name.
    """
    import hashlib
    import extract_rlib_elf as elf

    source = Path(fixture).read_text()
    success = True
    for prefix, machine, path in [("x86", 62, x86_rlib), ("aarch64", 183, aarch64_rlib)]:
        def literal(suffix, pattern):
            matches = re.findall(r"def " + prefix + suffix + r"\s*:\s*\w+\s*:=\s*" + pattern, source)
            if len(matches) != 1:
                raise ValueError(f"missing or ambiguous {prefix}{suffix}")
            return matches[0]
        if generation == "current":
            prefix = "currentX86" if machine == 62 else "currentAarch64"
        digest = literal("RcguElfSha256", r'"([0-9a-f]{64})"')
        if generation == "current":
            matches = re.findall(r"def " + prefix +
                r"RlibLiteral\s*:\s*Nat × Nat\s*:=\s*\(([0-9]+),\s*(0x[0-9a-fA-F]+)\)", source)
            if len(matches) != 1:
                raise ValueError(f"missing or ambiguous {prefix}RlibLiteral")
            size, packed = int(matches[0][0]), int(matches[0][1], 16)
        else:
            size = int(literal("RlibArchiveLen", r"([0-9]+)"))
            packed = int(literal("RlibArchiveNat", r"(0x[0-9a-fA-F]+)"), 16)
        archive = packed.to_bytes(size, "little")
        members = [m for m in elf.parse_ar_archive(archive) if m.payload.startswith(elf.ELF_MAGIC)]
        if len(members) != 1 or hashlib.sha256(members[0].payload).hexdigest() != digest:
            raise ValueError(f"{prefix}: fixture literal does not match its SHA-256 provenance")
        pinned = elf.parse_elf64_object(members[0].name, members[0].payload)
        _, _, fresh = elf.extract_qsag_elf_from_rlib(Path(path))
        if pinned.machine != machine or fresh.machine != machine:
            raise ValueError(f"{prefix}: incorrect ELF architecture")
        old = {symbol.name: symbol.code for symbol in pinned.qsag_symbols}
        new = {symbol.name: symbol.code for symbol in fresh.qsag_symbols}
        if len(old) != len(pinned.qsag_symbols) or len(new) != len(fresh.qsag_symbols):
            raise ValueError(f"{prefix}: duplicate kernel symbol")
        changed = [name for name in old if name in new and old[name] != new[name]]
        removed = [name for name in old if name not in new]
        added = [name for name in new if name not in old]
        same = len(old) - len(changed) - len(removed)
        for name in changed:
            print(f"{prefix}: kernel bytes differ: {name}: pinned {len(old[name])} B, "
                  f"fresh {len(new[name])} B", file=sys.stderr)
        for name in removed:
            print(f"{prefix}: pinned kernel absent from fresh build: {name}", file=sys.stderr)
        for name in added:
            print(f"{prefix}: fresh kernel absent from fixture: {name} ({len(new[name])} B)",
                  file=sys.stderr)
        kernels_match = not (changed or removed or added)
        object_match = fresh.sha256 == digest
        print(f"{prefix}: kernels identical {same}/{len(old)}, changed {len(changed)}, "
              f"removed {len(removed)}, unpinned new {len(added)}; "
              f"object digest pinned={digest} fresh={fresh.sha256}")
        if binding == "object":
            passed = object_match and kernels_match
        else:
            passed = kernels_match
        if passed:
            print(f"{prefix}: PASS ({binding} binding)")
        else:
            print(f"{prefix}: FAIL: stale fixture ({binding} binding): pinned={digest}, "
                  f"fresh={fresh.sha256}; regenerate fixtures and their certificates with the CI "
                  "toolchain", file=sys.stderr)
            success = False
    return success


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--elf-bin', action='append', default=[], help='final linked ELF, repeatable')
    parser.add_argument('--rlib', action='append', default=[], help='native archive or object, repeatable')
    parser.add_argument('--llvm-objdump')
    parser.add_argument('--require-bitslice', action=argparse.BooleanOptionalAction, default=True,
                        help='require every bitslice assembly kernel for the input architecture (default: enabled)')
    parser.add_argument('--require-namespace', action='append', default=[], choices=RUST_MODULES,
                        help='require this compiled Rust namespace; repeat for each required surface')
    parser.add_argument('--require-simd', action='store_true',
                        help='require every registered SIMD entrypoint for this architecture')
    parser.add_argument('--strict-rust-branches', action='store_true')
    parser.add_argument('--self-test', action='store_true')
    parser.add_argument('--check-fixtures', type=Path)
    parser.add_argument('--fixture-x86-rlib', type=Path)
    parser.add_argument('--fixture-aarch64-rlib', type=Path)
    parser.add_argument('--fixture-generation', choices=('historical', 'current'),
                        default='current', help='select the explicitly named archive generation; '
                        'freshness alone does not establish a Lean certificate')
    parser.add_argument('--fixture-binding', choices=('object', 'kernel-bytes'), default='object',
                        help='object: fresh ELF member byte-identical to the certified one; '
                             'kernel-bytes: identical qsag_asm_* symbol set and code bytes')
    parser.add_argument('--cross-aarch64-bitslice', action='store_true', help='cross-assemble and audit both AArch64 bitslice kernels')
    if any(arg in sys.argv for arg in ('--x86-asm-rs', '--aarch64-asm', '--extra-x86-obj',
                                      '--extra-rlib', '--aarch64-apple-rs', '--llvm-mc')):
        return legacy_main()
    args = parser.parse_args()
    print(f'{self_tests()} auditor self-tests passed')
    paths = args.elf_bin + args.rlib
    if not paths and not args.self_test and not args.cross_aarch64_bitslice and not args.check_fixtures:
        root = Path(__file__).resolve().parents[1]
        generation = 'current-elf' if args.fixture_generation == 'current' else 'historical-elf'
        paths = [str(root / 'lean/fixtures' / generation / f'{arch}.rlib')
                 for arch in ('x86_64', 'aarch64')]
        print(f'Default inventory: {generation}; retained archives, not a live rebuild')
    success = True
    if args.check_fixtures:
        if not args.fixture_x86_rlib or not args.fixture_aarch64_rlib:
            parser.error('--check-fixtures requires both fixture rlib paths')
        try:
            success = check_fixtures(args.check_fixtures, args.fixture_x86_rlib, args.fixture_aarch64_rlib,
                                     args.fixture_binding, args.fixture_generation)
        except (ValueError, OSError, OverflowError) as error:
            print(f'fixture provenance: FAIL: {error}', file=sys.stderr)
            success = False
    if args.cross_aarch64_bitslice:
        success = cross_aarch64_bitslice(args.llvm_objdump) and success
    for name in paths:
        try:
            if name in args.elf_bin and elf_header(Path(name).read_bytes())[0] not in (2, 3):
                raise ValueError('--elf-bin requires a linked ET_EXEC or ET_DYN image')
            success = audit(Path(name).resolve(), args.llvm_objdump, args.strict_rust_branches, args.require_bitslice, args.require_namespace, args.require_simd) and success
        except (ValueError, OSError, subprocess.CalledProcessError) as error:
            print(f'{name}: FAIL: {error}', file=sys.stderr)
            success = False
    return 0 if success else 1


if __name__ == '__main__':
    sys.exit(main())
