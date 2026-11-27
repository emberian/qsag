#!/usr/bin/env python3
"""
sync_dregg_sig.py — Deterministic bidirectional synchronization between `qsag`
(the canonical full-assurance superset) and `dregg-sig` (the standalone Rust export).

Modes:
  --diff   <dregg_sig_dir>   Report missing, extra, and semantically drifted files.
  --check  <dregg_sig_dir>   Exit 0 iff `dregg-sig` has zero semantic drift from `qsag`.
  --export <dregg_sig_dir>   Project `qsag` -> `dregg-sig` with deterministic renaming.
  --import <dregg_sig_dir>   Project `dregg-sig` -> `qsag` with inverse renaming.

Invariant preservation:
  - Cryptographic domain separation tags (`QSAG.*`), wire magics (`QSAGHQM2`, `QSAGZKH2`, `QSAGZKS2`,
    `QSHEM*`, `QSNULRG1`, etc.), BLAKE2 personalizations (`QSAG_Zcash*`), Bech32m HRPs
    (`qsp`, `qst`), and JSON schema identifiers (`qsag-migration-*-v2`, etc.) remain
    byte-for-byte identical across both repositories.
  - Package names (`qsag-*` <-> `dregg-sig-*`), Rust/ASM crate identifiers (`qsag_*` <->
    `dregg_sig_*`), workspace dependency paths, CLI binary names (`qsag` <-> `dregg-sig`),
    and runtime/benchmark environment variables (`QSAG_*` <-> `DREGG_SIG_*`, excluding the
    preserved subprocess IPC variables) map bijectively.

Rename rules are anchored so that data never moves with a crate name:
  - `qsag-<crate>` is a package name only when no further name character follows it, so
    `qsag-cred-spdz-voprf-share-v1`, `qsag-policy-ledger-v2` or `qsag-hem-quintic-proof-v2` stay.
  - `qsag_<crate>` is a crate identifier only at the start of an identifier (one leading
    underscore is allowed for Mach-O symbols), so `spec_qsag_agg_x` stays.
  - the bare CLI word `qsag` is never rewritten inside a byte string (`b"qsag kat ..."`).
  - GLSL sources and lines of prose that speak about `dregg-sig` itself are not path-rewritten.
"""

from __future__ import annotations

import argparse
import difflib
import os
import pathlib
import re
import shutil
import sys
from dataclasses import dataclass
from typing import Dict, Iterable, List, Optional, Tuple

# Ordered longest-first so compound names (`whir-verified`, `validation-zcash`) match first.
CRATE_SUFFIXES: Tuple[str, ...] = (
    "whir-verified",
    "validation-zcash",
    "verified",
    "migrate",
    "policy",
    "quorum",
    "accel",
    "addr",
    "core",
    "cred",
    "agg",
    "asm",
    "cli",
    "fts",
    "hd",
)

WORKSPACE_CRATES: Tuple[str, ...] = (
    "accel",
    "addr",
    "agg",
    "asm",
    "cli",
    "core",
    "cred",
    "fts",
    "hd",
    "migrate",
    "policy",
    "quorum",
)

# Child-process IPC environment variables intentionally kept with `QSAG_` in both repos.
PRESERVED_QSAG_ENV_VARS = frozenset(
    {
        "QSAG_SEAL_STORE_CHILD_PATH",
        "QSAG_VC_CHALLENGE_CHILD_DIR",
        "QSAG_VC_CHALLENGE_CHILD_ROLE",
        "QSAG_VOLATILE_MINT_MATRIX_CHILD",
        "QSAG_VOLATILE_WAISTBAND_CHILD",
    }
)

# Copied byte-for-byte in both directions.
VERBATIM_FILES = frozenset(
    {"rust-toolchain.toml", "LICENSE-APACHE", "LICENSE-MIT", "tests/kat_vectors.json", "fuzz/.gitignore"}
)
# The asm crate's compatibility entry point calls the root auditor in both layouts.
SHARED_ROOT_FILES = ("Cargo.toml", "rust-toolchain.toml", "LICENSE-APACHE", "LICENSE-MIT",
                     "scripts/audit_elf_ct.py")
# GLSL sources travel with the SPIR-V words compiled from them; their text is never rewritten.
VERBATIM_SUFFIXES: Tuple[str, ...] = (".comp",)

BINARY_EXTENSIONS = frozenset({".spv", ".png", ".jpg", ".pdf", ".bin"})

SKIP_DIR_NAMES = frozenset({"target", ".git", "__pycache__", ".DS_Store"})

VERIFIED_QSAG_ONLY_FILES = frozenset(
    {
        "Cargo.lock",
        "build.rs",
        "extraction-coverage.json",
        "extraction-coverage.md",
        "extraction-provenance.json",
        "rust-toolchain.toml",
        "tests/parity_qsag_core.rs",
    }
)

DREGG_ROOT_CARGO_TOML = """\
[workspace]
resolver = "2"
members = ["crates/*"]

[workspace.package]
version = "0.1.0"
edition = "2024"
license = "Apache-2.0 OR MIT"
authors = ["ember arlynx <ember@lunar.town>"]
rust-version = "1.99.1"

[profile.dev]
opt-level = 1

[profile.release]
opt-level = 3
lto = "thin"
codegen-units = 1
"""

DEFAULT_DREGG_README = """\
# dregg-sig

Standalone post-quantum threshold signing, succinct WHIR signature aggregation (`zk-Hem v2`),
and multi-chain / Zcash post-quantum ownership migration in `#![no_std]` safe Rust with zero
external `crates.io` library dependencies.
"""


def _qsag_env_to_dregg(match: re.Match[str]) -> str:
    tok = match.group(0)
    if tok in PRESERVED_QSAG_ENV_VARS:
        return tok
    return "DREGG_SIG_" + tok[len("QSAG_") :]


def _dregg_env_to_qsag(match: re.Match[str]) -> str:
    tok = match.group(0)
    return "QSAG_" + tok[len("DREGG_SIG_") :]


_RE_QSAG_ENV = re.compile(r"\bQSAG_[A-Z0-9_]+\b")
_RE_DREGG_ENV = re.compile(r"\bDREGG_SIG_[A-Z0-9_]+\b")

_NAME_END = r"(?![A-Za-z0-9_-])"
_IDENT_START = r"(?<![A-Za-z0-9])(?<![A-Za-z0-9]_)"
_HYPHEN_ALT = "|".join(re.escape(c) for c in CRATE_SUFFIXES)
_IDENT_ALT = "|".join(re.escape(c.replace("-", "_")) for c in CRATE_SUFFIXES)
_PATH_ALT = "|".join(re.escape(c) for c in WORKSPACE_CRATES)

# Package names: `qsag-core`, `qsag-asm/std`, `dep:qsag-accel`; not `qsag-cred-spdz-voprf-share-v1`.
_RE_QSAG_PKG = re.compile(rf"qsag-({_HYPHEN_ALT}){_NAME_END}")
_RE_DREGG_PKG = re.compile(rf"dregg-sig-({_HYPHEN_ALT}){_NAME_END}")
# Crate identifiers and `[_]qsag_asm_*` symbols; not `spec_qsag_agg_x`.
_RE_QSAG_IDENT = re.compile(rf"{_IDENT_START}qsag_({_IDENT_ALT})")
_RE_DREGG_IDENT = re.compile(rf"{_IDENT_START}dregg_sig_({_IDENT_ALT})")
# Repository paths in prose and scripts: `crates/qsag-agg/SECURITY.md` <-> `crates/agg/SECURITY.md`.
_RE_QSAG_PATH = re.compile(rf"(?<![A-Za-z0-9_-])crates/qsag-({_PATH_ALT}){_NAME_END}")
_RE_DREGG_PATH = re.compile(rf"(?<![A-Za-z0-9_-])crates/({_PATH_ALT}){_NAME_END}")
# The CLI's own name as a bare word. Excluded: byte strings (`b"qsag kat aggregate"` is signed
# data), names that continue (`qsag-secret-key-v1`, `.qsag-{stem}.anchor`), paths, and the test
# helper `fn qsag(`.
_CLI_WORD = r"(?<![A-Za-z0-9_.\-/])(?<!b\")(?<!b')%s(?![A-Za-z0-9_\-(])"
_RE_QSAG_CLI_WORD = re.compile(_CLI_WORD % "qsag")
_RE_DREGG_CLI_WORD = re.compile(_CLI_WORD % "dregg-sig")


def _is_verbatim(qsag_rel: str) -> bool:
    return qsag_rel in VERBATIM_FILES or qsag_rel.endswith(VERBATIM_SUFFIXES)


def _speaks_of_dregg(line: str) -> bool:
    return "dregg-sig" in line or "dregg_sig" in line


def _map_lines(text: str, pattern: "re.Pattern[str]", repl: str) -> str:
    """Apply `pattern` on every line that does not itself speak about `dregg-sig`.

    A line of qsag prose that names the fork (`its `crates/agg` is this crate`) carries dregg-sig
    paths on purpose. Such a line still names the fork after every other inverse rename has run,
    which is how the inverse direction recognises it.
    """
    return "\n".join(
        line if _speaks_of_dregg(line) else pattern.sub(repl, line) for line in text.split("\n")
    )


def _lock_sort_key(block: str) -> Tuple[str, Tuple[Tuple[int, ...], int, str], str]:
    """Cargo orders `[[package]]` tables by name, then semantic version, then source."""

    def field(name: str) -> str:
        m = re.search(rf'(?m)^{name} = "([^"]*)"$', block)
        return m.group(1) if m else ""

    core, _, pre = field("version").partition("+")[0].partition("-")
    numbers = tuple(int(x) if x.isdigit() else 0 for x in core.split("."))
    # A pre-release sorts before the release it precedes.
    return field("name"), (numbers, 0 if pre else 1, pre), field("source")


def _resort_lockfile(text: str) -> str:
    """Restore Cargo's ordering after package names changed.

    Cargo writes `[[package]]` tables and each `dependencies` array in sorted order and, under
    `--locked`, refuses a lockfile whose text is not what it would write itself.
    """
    parts = text.split("\n[[package]]\n")
    if len(parts) < 2:
        return text
    head, blocks = parts[0], parts[1:]
    tail = ""
    cut = blocks[-1].find("\n\n[")
    if cut != -1:
        blocks[-1], tail = blocks[-1][: cut + 1], blocks[-1][cut + 1 :]

    def sort_deps(block: str) -> str:
        def one(m: "re.Match[str]") -> str:
            # Entries are `name`, `name version` or `name version (source)`, ordered field-wise.
            items = sorted(
                (l for l in m.group(2).split("\n") if l),
                key=lambda l: l.strip().rstrip(",").strip('"').split(" "),
            )
            return m.group(1) + "\n".join(items) + "\n" + m.group(3)

        return re.sub(r"(?s)(dependencies = \[\n)(.*?)(\])", one, block)

    blocks = sorted((sort_deps(b) for b in blocks), key=_lock_sort_key)
    return head + "\n[[package]]\n" + "\n[[package]]\n".join(blocks) + tail


def transform_text_qsag_to_dregg(text: str, qsag_rel: str) -> str:
    """Deterministic forward projection of file contents (`qsag` -> `dregg-sig`)."""
    if qsag_rel == "Cargo.toml":
        return DREGG_ROOT_CARGO_TOML
    if _is_verbatim(qsag_rel):
        return text

    out = text

    # 1. Special handling for standalone Aeneas verified manifests when joining `crates/*` workspace.
    if qsag_rel == "aeneas/qsag-verified/Cargo.toml":
        # The table goes together with the blank line that follows it, so that the inverse
        # (which inserts table + blank line before `[features]`) restores the same bytes.
        out = re.sub(
            r"\n\[\[test\]\]\nname = \"parity_qsag_core\"\nharness = false\n\n",
            "\n",
            out,
        )
        out = re.sub(
            r"\n# Keep MIR extraction independent of the production workspace\.\n\[workspace\]\s*$",
            "\n",
            out,
        )
    elif qsag_rel == "aeneas/qsag-whir-verified/Cargo.toml":
        out = re.sub(r"\n\[workspace\]\s*$", "\n", out)

    # 2. Dependency path rewrites in Cargo.toml files.
    if qsag_rel.endswith("Cargo.toml"):
        out = out.replace('path = "../../aeneas/qsag-verified"', 'path = "../verified"')
        out = out.replace('path = "../../aeneas/qsag-whir-verified"', 'path = "../whir-verified"')
        for c in WORKSPACE_CRATES:
            out = out.replace(f'path = "../../crates/qsag-{c}"', f'path = "../../crates/{c}"')
            out = out.replace(f'path = "../crates/qsag-{c}"', f'path = "../crates/{c}"')
            out = out.replace(f'path = "../qsag-{c}"', f'path = "../{c}"')
        out = out.replace(
            'path = "../aeneas/qsag-verified"',
            'path = "../crates/verified"',
        )
        out = out.replace(
            'path = "../aeneas/qsag-whir-verified"',
            'path = "../crates/whir-verified"',
        )
        if qsag_rel == "crates/qsag-cli/Cargo.toml":
            out = re.sub(r'(\[\[bin\]\]\s*\nname\s*=\s*)"qsag"', r'\1"dregg-sig"', out)
        if qsag_rel == "fuzz/Cargo.toml":
            out = out.replace('name = "qsag-fuzz"', 'name = "dregg-sig-fuzz"')
        out = out.replace("for qsag", "for dregg-sig")
        out = out.replace("of qsag ", "of dregg-sig ")

    # 3. Doc / script crate path references (`crates/qsag-foo` -> `crates/foo`). This runs before
    #    the package-name rule, which would otherwise turn the path into `crates/dregg-sig-foo`.
    out = _map_lines(out, _RE_QSAG_PATH, r"crates/\1")

    # 4. Package names & Rust/ASM crate identifiers.
    out = _RE_QSAG_PKG.sub(r"dregg-sig-\1", out)
    out = _RE_QSAG_IDENT.sub(r"dregg_sig_\1", out)

    # 5. CLI binary & test macro references.
    out = out.replace("CARGO_BIN_EXE_qsag", "CARGO_BIN_EXE_dregg-sig")
    if qsag_rel.startswith("crates/qsag-cli/"):
        out = _RE_QSAG_CLI_WORD.sub("dregg-sig", out)

    # 6. Runtime / benchmark environment variables (`QSAG_*` -> `DREGG_SIG_*`).
    out = _RE_QSAG_ENV.sub(_qsag_env_to_dregg, out)

    if qsag_rel.endswith("Cargo.lock"):
        out = _resort_lockfile(out)

    return out


def transform_text_dregg_to_qsag(text: str, qsag_rel: str) -> str:
    """Deterministic inverse projection of file contents (`dregg-sig` -> `qsag`)."""
    if _is_verbatim(qsag_rel):
        return text

    out = text

    # 1. Dependency path rewrites in Cargo.toml files.
    if qsag_rel.endswith("Cargo.toml"):
        if qsag_rel == "fuzz/Cargo.toml":
            out = out.replace('path = "../crates/verified"', 'path = "../aeneas/qsag-verified"')
            out = out.replace('path = "../crates/whir-verified"', 'path = "../aeneas/qsag-whir-verified"')
            for c in WORKSPACE_CRATES:
                out = out.replace(f'path = "../crates/{c}"', f'path = "../crates/qsag-{c}"')
        elif qsag_rel == "validation/zcash/Cargo.toml":
            for c in WORKSPACE_CRATES:
                out = out.replace(f'path = "../../crates/{c}"', f'path = "../../crates/qsag-{c}"')
        else:
            out = out.replace('path = "../verified"', 'path = "../../aeneas/qsag-verified"')
            out = out.replace('path = "../whir-verified"', 'path = "../../aeneas/qsag-whir-verified"')
            for c in WORKSPACE_CRATES:
                out = out.replace(f'path = "../{c}"', f'path = "../qsag-{c}"')
        if qsag_rel == "crates/qsag-cli/Cargo.toml":
            out = re.sub(r'(\[\[bin\]\]\s*\nname\s*=\s*)"dregg-sig"', r'\1"qsag"', out)
        if qsag_rel == "fuzz/Cargo.toml":
            out = out.replace('name = "dregg-sig-fuzz"', 'name = "qsag-fuzz"')
        out = out.replace("for dregg-sig", "for qsag")
        out = out.replace("of dregg-sig ", "of qsag ")

    # 2. Package names & Rust/ASM crate identifiers.
    out = _RE_DREGG_PKG.sub(r"qsag-\1", out)
    out = _RE_DREGG_IDENT.sub(r"qsag_\1", out)

    # 3. CLI binary & test macro references.
    out = out.replace("CARGO_BIN_EXE_dregg-sig", "CARGO_BIN_EXE_qsag")
    if qsag_rel.startswith("crates/qsag-cli/"):
        out = _RE_DREGG_CLI_WORD.sub("qsag", out)

    # 4. Runtime / benchmark environment variables (`DREGG_SIG_*` -> `QSAG_*`).
    out = _RE_DREGG_ENV.sub(_dregg_env_to_qsag, out)

    # 5. Doc / script crate path references (`crates/foo` -> `crates/qsag-foo`). Lines that still
    #    name `dregg-sig` after steps 1-4 are prose about the fork and keep its paths.
    out = _map_lines(out, _RE_DREGG_PATH, r"crates/qsag-\1")

    # 6. Restore standalone Aeneas manifest footers if stripped.
    if qsag_rel == "aeneas/qsag-verified/Cargo.toml":
        if 'name = "parity_qsag_core"' not in out:
            out = out.replace(
                "\n[features]\n",
                '\n[[test]]\nname = "parity_qsag_core"\nharness = false\n\n[features]\n',
                1,
            )
        if "[workspace]" not in out:
            out = out.rstrip() + "\n\n# Keep MIR extraction independent of the production workspace.\n[workspace]\n"
    elif qsag_rel == "aeneas/qsag-whir-verified/Cargo.toml":
        if "[workspace]" not in out:
            out = out.rstrip() + "\n[workspace]\n"

    if qsag_rel.endswith("Cargo.lock"):
        out = _resort_lockfile(out)

    return out


def _iter_files(base: pathlib.Path) -> Iterable[pathlib.Path]:
    if not base.exists():
        return
    for root, dirs, files in os.walk(base):
        dirs[:] = sorted(d for d in dirs if d not in SKIP_DIR_NAMES)
        for fname in sorted(files):
            if fname in SKIP_DIR_NAMES or fname.endswith(".pyc"):
                continue
            yield pathlib.Path(root) / fname


def collect_qsag_mapped_files(qsag_root: pathlib.Path) -> Dict[str, str]:
    """Return `{qsag_rel: dregg_rel}` for all files in `qsag` belonging to the `dregg-sig` projection."""
    mapping: Dict[str, str] = {}

    for root_file in SHARED_ROOT_FILES:
        if (qsag_root / root_file).is_file():
            mapping[root_file] = root_file

    if (qsag_root / "tests/kat_vectors.json").is_file():
        mapping["tests/kat_vectors.json"] = "tests/kat_vectors.json"

    for c in WORKSPACE_CRATES:
        qdir = qsag_root / "crates" / f"qsag-{c}"
        for f in _iter_files(qdir):
            sub = f.relative_to(qdir).as_posix()
            if sub == "Cargo.lock":
                continue
            mapping[f"crates/qsag-{c}/{sub}"] = f"crates/{c}/{sub}"

    for q_sub, d_sub, skip_set in (
        ("aeneas/qsag-verified", "crates/verified", VERIFIED_QSAG_ONLY_FILES),
        ("aeneas/qsag-whir-verified", "crates/whir-verified", VERIFIED_QSAG_ONLY_FILES),
    ):
        qdir = qsag_root / q_sub
        for f in _iter_files(qdir):
            sub = f.relative_to(qdir).as_posix()
            if sub in skip_set:
                continue
            mapping[f"{q_sub}/{sub}"] = f"{d_sub}/{sub}"

    fuzz_dir = qsag_root / "fuzz"
    for f in _iter_files(fuzz_dir):
        sub = f.relative_to(fuzz_dir).as_posix()
        if sub == "Cargo.lock" or sub.startswith(("corpus/", "artifacts/")):
            continue
        mapping[f"fuzz/{sub}"] = f"fuzz/{sub}"

    val_zcash = qsag_root / "validation/zcash"
    for f in _iter_files(val_zcash):
        sub = f.relative_to(val_zcash).as_posix()
        mapping[f"validation/zcash/{sub}"] = f"validation/zcash/{sub}"

    return mapping


def collect_dregg_mapped_files(dregg_root: pathlib.Path) -> Dict[str, str]:
    """Return `{dregg_rel: qsag_rel}` for all managed files present in `dregg_root`.

    Includes any extra or retired crate directories under `crates/` (e.g. `crates/ass2`) and
    retired root directories (`hardware/`, `history/`) so `--diff` / `--check` flag them and
    `--export` removes them cleanly under `members = ["crates/*"]`.
    """
    mapping: Dict[str, str] = {}

    for root_file in SHARED_ROOT_FILES:
        if (dregg_root / root_file).is_file():
            mapping[root_file] = root_file

    if (dregg_root / "tests/kat_vectors.json").is_file():
        mapping["tests/kat_vectors.json"] = "tests/kat_vectors.json"

    crates_dir = dregg_root / "crates"
    extra_crates: List[str] = []
    if crates_dir.is_dir():
        extra_crates = sorted(
            p.name
            for p in crates_dir.iterdir()
            if p.is_dir()
            and p.name not in SKIP_DIR_NAMES
            and p.name not in WORKSPACE_CRATES
            and p.name not in {"verified", "whir-verified"}
        )

    for c in (*WORKSPACE_CRATES, *extra_crates):
        ddir = crates_dir / c
        for f in _iter_files(ddir):
            sub = f.relative_to(ddir).as_posix()
            if sub == "Cargo.lock":
                continue
            mapping[f"crates/{c}/{sub}"] = f"crates/qsag-{c}/{sub}"

    for d_sub, q_sub in (
        ("crates/verified", "aeneas/qsag-verified"),
        ("crates/whir-verified", "aeneas/qsag-whir-verified"),
    ):
        ddir = dregg_root / d_sub
        for f in _iter_files(ddir):
            sub = f.relative_to(ddir).as_posix()
            if sub == "Cargo.lock":
                continue
            mapping[f"{d_sub}/{sub}"] = f"{q_sub}/{sub}"

    for legacy_root in ("hardware", "history"):
        ldir = dregg_root / legacy_root
        for f in _iter_files(ldir):
            sub = f.relative_to(ldir).as_posix()
            mapping[f"{legacy_root}/{sub}"] = f"{legacy_root}/{sub}"

    fuzz_dir = dregg_root / "fuzz"
    for f in _iter_files(fuzz_dir):
        sub = f.relative_to(fuzz_dir).as_posix()
        if sub == "Cargo.lock" or sub.startswith(("corpus/", "artifacts/")):
            continue
        mapping[f"fuzz/{sub}"] = f"fuzz/{sub}"

    val_zcash = dregg_root / "validation/zcash"
    for f in _iter_files(val_zcash):
        sub = f.relative_to(val_zcash).as_posix()
        mapping[f"validation/zcash/{sub}"] = f"validation/zcash/{sub}"

    return mapping


def _prune_empty_parents(directory: pathlib.Path, stop_at: pathlib.Path) -> None:
    cur = directory
    stop = stop_at.resolve()
    while cur.exists() and cur.resolve() != stop:
        try:
            cur.rmdir()
        except OSError:
            break
        cur = cur.parent


def _is_retired_qsag_target(qsag_rel: str) -> bool:
    if qsag_rel.startswith(("hardware/", "history/")):
        return True
    if qsag_rel.startswith("crates/qsag-"):
        crate = qsag_rel.split("/", 2)[1].removeprefix("qsag-")
        return crate not in WORKSPACE_CRATES
    return False


def is_binary_path(rel_path: str) -> bool:
    return pathlib.Path(rel_path).suffix.lower() in BINARY_EXTENSIONS


def project_file_to_dregg_bytes(qsag_root: pathlib.Path, qsag_rel: str) -> bytes:
    src = qsag_root / qsag_rel
    raw = src.read_bytes()
    if is_binary_path(qsag_rel):
        return raw
    text = raw.decode("utf-8")
    projected = transform_text_qsag_to_dregg(text, qsag_rel)
    return projected.encode("utf-8")


def project_file_to_qsag_bytes(dregg_root: pathlib.Path, dregg_rel: str, qsag_rel: str) -> bytes:
    src = dregg_root / dregg_rel
    raw = src.read_bytes()
    if is_binary_path(dregg_rel):
        return raw
    text = raw.decode("utf-8")
    projected = transform_text_dregg_to_qsag(text, qsag_rel)
    return projected.encode("utf-8")


@dataclass
class DiffReport:
    only_in_qsag: List[Tuple[str, str]]
    only_in_dregg: List[Tuple[str, str]]
    modified: List[Tuple[str, str, List[str]]]

    @property
    def is_clean(self) -> bool:
        return not self.only_in_qsag and not self.only_in_dregg and not self.modified


def compute_diff(qsag_root: pathlib.Path, dregg_root: pathlib.Path, context_lines: int = 3) -> DiffReport:
    q_map = collect_qsag_mapped_files(qsag_root)
    d_map = collect_dregg_mapped_files(dregg_root)

    q_by_dregg = {d_rel: q_rel for q_rel, d_rel in q_map.items()}
    all_dregg_rels = sorted(set(q_by_dregg.keys()) | set(d_map.keys()))

    only_q: List[Tuple[str, str]] = []
    only_d: List[Tuple[str, str]] = []
    modified: List[Tuple[str, str, List[str]]] = []

    for d_rel in all_dregg_rels:
        in_q = d_rel in q_by_dregg
        in_d = d_rel in d_map
        if in_q and not in_d:
            only_q.append((q_by_dregg[d_rel], d_rel))
        elif in_d and not in_q:
            only_d.append((d_map[d_rel], d_rel))
        else:
            q_rel = q_by_dregg[d_rel]
            expected_bytes = project_file_to_dregg_bytes(qsag_root, q_rel)
            actual_bytes = (dregg_root / d_rel).read_bytes()
            if expected_bytes != actual_bytes:
                if is_binary_path(d_rel):
                    diff_lines = [f"Binary files qsag:{q_rel} (projected) and dregg-sig:{d_rel} differ"]
                else:
                    exp_lines = expected_bytes.decode("utf-8", errors="replace").splitlines()
                    act_lines = actual_bytes.decode("utf-8", errors="replace").splitlines()
                    diff_lines = list(
                        difflib.unified_diff(
                            exp_lines,
                            act_lines,
                            fromfile=f"qsag:{q_rel} (projected)",
                            tofile=f"dregg-sig:{d_rel}",
                            lineterm="",
                            n=context_lines,
                        )
                    )
                modified.append((q_rel, d_rel, diff_lines))

    return DiffReport(only_in_qsag=only_q, only_in_dregg=only_d, modified=modified)


def run_export(qsag_root: pathlib.Path, dregg_root: pathlib.Path, dry_run: bool = False) -> Tuple[int, int, int]:
    q_map = collect_qsag_mapped_files(qsag_root)
    existing_d = collect_dregg_mapped_files(dregg_root) if dregg_root.exists() else {}
    target_dregg_rels = set(q_map.values())

    written = 0
    unchanged = 0
    removed = 0

    if not dry_run:
        dregg_root.mkdir(parents=True, exist_ok=True)
        readme_path = dregg_root / "README.md"
        if not readme_path.exists():
            readme_path.write_text(DEFAULT_DREGG_README, encoding="utf-8")

    for q_rel, d_rel in sorted(q_map.items(), key=lambda kv: kv[1]):
        projected = project_file_to_dregg_bytes(qsag_root, q_rel)
        dst = dregg_root / d_rel
        if dst.is_file() and dst.read_bytes() == projected:
            unchanged += 1
            continue
        written += 1
        if not dry_run:
            dst.parent.mkdir(parents=True, exist_ok=True)
            dst.write_bytes(projected)
            shutil.copymode(qsag_root / q_rel, dst)

    for d_rel in sorted(existing_d.keys()):
        if d_rel not in target_dregg_rels:
            removed += 1
            if not dry_run:
                stale = dregg_root / d_rel
                if stale.is_file():
                    stale.unlink()
                    _prune_empty_parents(stale.parent, dregg_root)

    return written, unchanged, removed


def run_import(qsag_root: pathlib.Path, dregg_root: pathlib.Path, dry_run: bool = False) -> Tuple[int, int, int]:
    if not dregg_root.is_dir():
        raise FileNotFoundError(f"dregg-sig directory does not exist: {dregg_root}")

    d_map = collect_dregg_mapped_files(dregg_root)
    retired = [(d_rel, q_rel) for d_rel, q_rel in sorted(d_map.items()) if _is_retired_qsag_target(q_rel)]
    if retired:
        sample = ", ".join(f"{d_rel} -> {q_rel}" for d_rel, q_rel in retired[:5])
        raise ValueError(f"refusing to import retired paths from dregg-sig ({sample})")
    existing_q = collect_qsag_mapped_files(qsag_root)
    imported_q_rels = set(d_map.values())

    written = 0
    unchanged = 0
    removed = 0

    for d_rel, q_rel in sorted(d_map.items(), key=lambda kv: kv[1]):
        # Never overwrite root Cargo.toml of qsag from dregg-sig's wildcard manifest.
        if q_rel == "Cargo.toml" and (qsag_root / "Cargo.toml").is_file():
            unchanged += 1
            continue
        projected = project_file_to_qsag_bytes(dregg_root, d_rel, q_rel)
        dst = qsag_root / q_rel
        if dst.is_file() and dst.read_bytes() == projected:
            unchanged += 1
            continue
        written += 1
        if not dry_run:
            dst.parent.mkdir(parents=True, exist_ok=True)
            dst.write_bytes(projected)
            shutil.copymode(dregg_root / d_rel, dst)

    for q_rel in sorted(existing_q.keys()):
        # Older exports carried only the asm wrapper. Keep its canonical implementation.
        if q_rel not in imported_q_rels and q_rel not in {"Cargo.toml", "scripts/audit_elf_ct.py"}:
            removed += 1
            if not dry_run:
                stale = qsag_root / q_rel
                if stale.is_file():
                    stale.unlink()
                    _prune_empty_parents(stale.parent, qsag_root)

    return written, unchanged, removed


def main(argv: Optional[List[str]] = None) -> int:
    default_qsag = pathlib.Path(__file__).resolve().parent.parent
    parser = argparse.ArgumentParser(
        description="Deterministic bidirectional sync tool between `qsag` and `dregg-sig`."
    )
    parser.add_argument(
        "--qsag",
        type=pathlib.Path,
        default=default_qsag,
        help="Path to the `qsag` workspace root (default: parent of scripts/).",
    )
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument(
        "--diff",
        metavar="DREGG_SIG_DIR",
        type=pathlib.Path,
        help="Show semantic file/line deltas between `qsag` and `DREGG_SIG_DIR`.",
    )
    group.add_argument(
        "--check",
        metavar="DREGG_SIG_DIR",
        type=pathlib.Path,
        help="Exit 0 iff `DREGG_SIG_DIR` has zero semantic drift from `qsag`.",
    )
    group.add_argument(
        "--export",
        metavar="DREGG_SIG_DIR",
        type=pathlib.Path,
        help="Project `qsag` into standalone `dregg-sig` layout at `DREGG_SIG_DIR`.",
    )
    group.add_argument(
        "--import",
        dest="import_dir",
        metavar="DREGG_SIG_DIR",
        type=pathlib.Path,
        help="Import standalone `dregg-sig` changes from `DREGG_SIG_DIR` into `--qsag`.",
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="For `--export` / `--import`: compute counts without writing to disk.",
    )
    parser.add_argument(
        "--summary-only",
        action="store_true",
        help="For `--diff`: print file-level summary without full unified hunks.",
    )

    args = parser.parse_args(argv)
    qsag_root = args.qsag.resolve()
    if not (qsag_root / "Cargo.toml").is_file():
        print(f"error: invalid --qsag root (missing Cargo.toml): {qsag_root}", file=sys.stderr)
        return 2

    if args.diff is not None or args.check is not None:
        dregg_root = (args.diff or args.check).resolve()
        if not dregg_root.is_dir():
            print(f"error: dregg-sig directory not found: {dregg_root}", file=sys.stderr)
            return 2
        report = compute_diff(qsag_root, dregg_root)
        print(
            f"sync_dregg_sig summary: "
            f"only_in_qsag={len(report.only_in_qsag)} "
            f"only_in_dregg_sig={len(report.only_in_dregg)} "
            f"semantically_modified={len(report.modified)}"
        )
        for q_rel, d_rel in report.only_in_qsag:
            print(f"  + [only in qsag]      {q_rel} -> {d_rel}")
        for q_rel, d_rel in report.only_in_dregg:
            print(f"  - [only in dregg-sig] {d_rel} (maps to {q_rel})")
        for q_rel, d_rel, diff_lines in report.modified:
            added = sum(1 for l in diff_lines if l.startswith("+") and not l.startswith("+++"))
            removed = sum(1 for l in diff_lines if l.startswith("-") and not l.startswith("---"))
            print(f"  ~ [modified]          {q_rel} <-> {d_rel} (+{added}/-{removed} lines)")
            if args.diff is not None and not args.summary_only:
                for line in diff_lines:
                    print(f"      {line}")

        if args.check is not None:
            if report.is_clean:
                # The text projection is itself under test. A new rename rule could
                # change a protocol label identically in both the export and --diff.
                from sync_domain_labels import projected_label_differences
                errors = projected_label_differences(qsag_root, dregg_root)
                if errors:
                    for error in errors:
                        print(f"FAIL: {error}", file=sys.stderr)
                    return 1
                print("OK: zero semantic drift between qsag and dregg-sig.")
                return 0
            print("FAIL: semantic drift detected between qsag and dregg-sig.", file=sys.stderr)
            return 1
        return 0

    if args.export is not None:
        dregg_root = args.export.resolve()
        written, unchanged, removed = run_export(qsag_root, dregg_root, dry_run=args.dry_run)
        mode = "dry-run export" if args.dry_run else "exported"
        print(
            f"{mode}: qsag ({qsag_root}) -> dregg-sig ({dregg_root}): "
            f"written={written} unchanged={unchanged} removed={removed}"
        )
        return 0

    if args.import_dir is not None:
        dregg_root = args.import_dir.resolve()
        written, unchanged, removed = run_import(qsag_root, dregg_root, dry_run=args.dry_run)
        mode = "dry-run import" if args.dry_run else "imported"
        print(
            f"{mode}: dregg-sig ({dregg_root}) -> qsag ({qsag_root}): "
            f"written={written} unchanged={unchanged} removed={removed}"
        )
        return 0

    return 2


if __name__ == "__main__":
    sys.exit(main())
