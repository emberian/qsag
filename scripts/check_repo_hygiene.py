#!/usr/bin/env python3
"""Fail-closed repository hygiene and buried-identifier gate (`qsag`).

Rejects any tracked or non-`history/` workspace file that re-introduces:
  1. Leaked internal development/agent/ticket/stage/wave paths or filenames;
  2. Banned internal jargon (`unified-stage`, `stage2-quintic`, `wave_x`, `wave-x`,
     `e12_`, `p1_06`, `BACKLOG-`, `fable-`, `claude-fable`, `astra_`, `subcarbon`,
     `RetiredUnpackedCounter`, `X5-*`, `FB5`, `rust-spec-parity`, `stage3_pors`,
     `LegacyCommitmentKind`, `LegacyOwnershipWitness`, hardcoded wave/deep paths);
  3. Buried v1 identifiers (`GoldilocksExt4`, `WhirSecurityRegime`, `BciksJohnson*`,
     `SuccinctHierarchicalHemAggregate`, `MergeNode::Branch`, `CoZK`,
     `QSAG_BENCH_REGIME`, `CARGO_PROFILE_RELEASE_CODEGEN_UNITS=16`, and
     `Nangate45` / `ASAP7` / `Dregg-180` outside `history/` and the single explicit
     non-manufacturable library exclusion note in `hardware/asic/synth/RESULTS.md`).

Preserves genuine domain terms:
  - `Wave32` GPU subgroup width
  - `QSAG-WAVE-*` RSS256 barrier domain tags
  - `StepOutcome::Retired` instruction retirement
  - `deployed_stage1_*` WHIR round-1 schedule identifiers
  - `Stage-2` hardware DSP pipeline stage comments
  - `sponge12_*` / `*State12_*` width-12 Poseidon2 identifiers
"""

from __future__ import annotations

import argparse
import os
from pathlib import Path
import re
import subprocess
import sys
from typing import Iterable, List, Sequence, Tuple

ROOT = Path(__file__).resolve().parents[1]
SELF_REL = "scripts/check_repo_hygiene.py"

SKIP_DIRS = frozenset(
    {
        ".git",
        ".lake",
        "target",
        "__pycache__",
        ".venv",
        "node_modules",
        "obj_dir",
        "sim_build",
        "work",
        "work_tmp",
        "work_hier",
        "mutants_out",
    }
)

BINARY_SUFFIXES = frozenset(
    {
        ".spv",
        ".png",
        ".jpg",
        ".jpeg",
        ".gif",
        ".ico",
        ".pdf",
        ".bin",
        ".bit",
        ".gds",
        ".oas",
        ".odb",
        ".spef",
        ".lib",
        ".lef",
        ".vcd",
        ".fst",
        ".ghw",
        ".gz",
        ".tgz",
        ".tar",
        ".zip",
        ".rlib",
        ".o",
        ".a",
        ".so",
        ".dylib",
        ".pyc",
        ".olean",
        ".ilean",
        ".llbc",
    }
)

# Paths (relative to repo root) that must never exist in a clean checkout.
FORBIDDEN_REL_PATHS: Tuple[str, ...] = (
    "scratch",
    "fable_hostile_audit.md",
    "REPORT.md",
    "hardware/asic/tb/d1_logs",
    "hardware/asic/synth/run_openroad.py",
    "hardware/asic/synth/render_routed_png.py",
    "hardware/fpga/build/verif_logs/retired_names.log",
    "hardware/ass2/pnr/LAST_MSG.md",
    "crates/qsag-accel/tests/e12_planted_fault_all10.rs",
    "validation/tests/wave_x5_wire_mutation_campaign.rs",
    "crates/qsag-migrate/src/legacy.rs",
)

FORBIDDEN_GLOB_PATTERNS: Tuple[str, ...] = (
    "history/dregg180-latch-prototype/scripts/astra_*.sh",
)

# Banned internal jargon across ALL non-`history/` files (including `lean/`).
JARGON_RULES: Tuple[Tuple[str, re.Pattern[str]], ...] = (
    ("unified-stage", re.compile(r"(?i)unified[-_]stage")),
    ("stage2-quintic", re.compile(r"(?i)stage2[-_]quintic")),
    ("wave_x", re.compile(r"(?i)wave_x")),
    ("wave-x", re.compile(r"(?i)wave-x")),
    ("e12_", re.compile(r"(?<![A-Za-z0-9])e12_[A-Za-z0-9_]*")),
    ("p1_06", re.compile(r"(?:(?<![A-Za-z0-9])|_)p1_06\b")),
    ("BACKLOG-", re.compile(r"BACKLOG-")),
    ("fable-", re.compile(r"(?i)fable-")),
    ("claude-fable", re.compile(r"(?i)claude[-_]fable")),
    ("astra_", re.compile(r"(?:(?<![A-Za-z0-9])|_)astra_[A-Za-z0-9_]*|dregg180-astra")),
    ("subcarbon", re.compile(r"(?i)subcarbon")),
    ("RetiredUnpackedCounter", re.compile(r"\bRetiredUnpackedCounter\b")),
    ("LegacyCommitmentKind", re.compile(r"\bLegacyCommitmentKind\b")),
    ("LegacyOwnershipWitness", re.compile(r"\bLegacyOwnershipWitness\b")),
    ("X5-ticket", re.compile(r"\bX5-\d+[a-z]?\b")),
    ("FB5-jargon", re.compile(r"\bFB5\b")),
    ("rust-spec-parity", re.compile(r"rust-spec-parity")),
    ("stage3_pors", re.compile(r"\bstage3_pors")),
    ("hardcoded-wave-path", re.compile(r"/(?:home/build|work)/wave-[A-Za-z0-9_-]+|/var/tmp/deep\d+-[A-Za-z0-9_-]+")),
    ("internal-hostname", re.compile(r"\b(?:bb2|hbox)\b")),
    ("swarm-build-jargon", re.compile(r"\bswarm-(?:build|qsag|obend|asic)\b|\bSWARM_MEM_MAX\b")),
    ("internal-lane-worktree", re.compile(r"\bp-ass2-lane\d*\b|\bverify_lane\d+\b|\bwt-s2-[A-Za-z0-9_-]*|/home/build/qsag-(?:ni-asic|ni-fast|obend)\b")),
)

# Buried v1 identifiers banned across ALL non-`history/` files (including `lean/`),
# with the single documented library-note allowance in `hardware/asic/synth/RESULTS.md`.
GLOBAL_BURIED_RULES: Tuple[Tuple[str, re.Pattern[str]], ...] = (
    ("SuccinctHierarchicalHemAggregate", re.compile(r"\bSuccinctHierarchicalHemAggregate\b")),
    ("MergeNode::Branch", re.compile(r"MergeNode::Branch")),
    ("Nangate45", re.compile(r"(?i)\bnangate45\b")),
    ("ASAP7", re.compile(r"(?i)\basap7\b")),
    ("Dregg-180", re.compile(r"(?i)\bdregg-?180\b")),
    ("CoZK", re.compile(r"\bCoZK\b")),
    ("QSAG_BENCH_REGIME", re.compile(r"\b(?:QSAG|DREGG_SIG)_BENCH_REGIME\b")),
    (
        "CARGO_PROFILE_RELEASE_CODEGEN_UNITS=16",
        re.compile(r"CARGO_PROFILE_RELEASE_CODEGEN_UNITS\s*=\s*['\"]?16\b"),
    ),
)

# Buried v1 Rust/doc aggregation identifiers banned in all non-`history/` files outside
# the constructive Lean mathematical library (`lean/`, `validation/lean/`).
NON_LEAN_BURIED_RULES: Tuple[Tuple[str, re.Pattern[str]], ...] = (
    ("GoldilocksExt4", re.compile(r"\bGoldilocksExt4\b")),
    ("WhirSecurityRegime", re.compile(r"\bWhirSecurityRegime\b")),
    ("BciksJohnson", re.compile(r"\bBciksJohnson[A-Za-z0-9_]*\b")),
    ("v1-regime-4", re.compile(r"\bregime\s*(?:=|\s)\s*4\b")),
)

_FAST_TEXT_PREFILTER = re.compile(
    r"(?i)unified[-_]stage|stage2[-_]quintic|wave[-_]x|(?<![A-Za-z0-9])e12_|p1_06|BACKLOG-|"
    r"fable-|claude[-_]fable|astra_|dregg180-astra|subcarbon|RetiredUnpackedCounter|"
    r"LegacyCommitmentKind|LegacyOwnershipWitness|\bX5-\d|\bFB5\b|rust-spec-parity|"
    r"stage3_pors|/(?:home/build|work)/wave-|/var/tmp/deep\d+-|"
    r"\bbb2\b|\bhbox\b|swarm-|SWARM_MEM_MAX|p-ass2-lane|verify_lane|wt-s2-|/home/build/qsag-|"
    r"SuccinctHierarchicalHemAggregate|MergeNode::Branch|nangate45|asap7|dregg-?180|"
    r"\bCoZK\b|_BENCH_REGIME|CARGO_PROFILE_RELEASE_CODEGEN_UNITS|"
    r"GoldilocksExt4|WhirSecurityRegime|BciksJohnson|\bregime\s*(?:=|\s)\s*4\b"
)


def is_results_library_exclusion_line(rel_path: str, line: str) -> bool:
    """Allow only the explicit non-manufacturable academic library exclusion note in RESULTS.md."""
    if rel_path != "hardware/asic/synth/RESULTS.md":
        return False
    stripped = line.strip()
    return (
        stripped.startswith("> **Library note:**")
        and "non-manufacturable academic reference libraries" in stripped
        and "excluded from foundry signoff" in stripped
    )


def scan_text(rel_path: str, text: str) -> List[Tuple[int, str, str]]:
    """Scan `text` at `rel_path` and return `(lineno, rule_name, snippet)` violations."""
    if rel_path == SELF_REL or rel_path.startswith("history/"):
        return []

    in_lean_math_tree = rel_path.startswith(("lean/", "validation/lean/"))
    violations: List[Tuple[int, str, str]] = []

    for rule_name, pat in JARGON_RULES:
        if pat.search(rel_path):
            violations.append((0, f"path:{rule_name}", rel_path))

    if not _FAST_TEXT_PREFILTER.search(text):
        return violations

    def _line_at(pos: int) -> Tuple[int, str]:
        lineno = text.count("\n", 0, pos) + 1
        line_start = text.rfind("\n", 0, pos) + 1
        line_end = text.find("\n", pos)
        if line_end == -1:
            line_end = len(text)
        return lineno, text[line_start:line_end]

    seen_hits: set[Tuple[int, str]] = set()
    active_rules = list(JARGON_RULES) + list(GLOBAL_BURIED_RULES)
    if not in_lean_math_tree:
        active_rules.extend(NON_LEAN_BURIED_RULES)

    for rule_name, pat in active_rules:
        for m in pat.finditer(text):
            lineno, raw_line = _line_at(m.start())
            if (lineno, rule_name) in seen_hits:
                continue
            if rule_name in ("Nangate45", "ASAP7") and is_results_library_exclusion_line(
                rel_path, raw_line
            ):
                continue
            seen_hits.add((lineno, rule_name))
            violations.append((lineno, rule_name, raw_line.strip()[:140]))

    violations.sort(key=lambda item: (item[0], item[1]))
    return violations


def iter_candidate_files(repo_root: Path) -> Iterable[Path]:
    """Yield candidate files from git index if present, plus clean working-tree walk."""
    seen: set[Path] = set()
    git_dir = repo_root / ".git"
    if git_dir.exists():
        proc = subprocess.run(
            ["git", "-C", str(repo_root), "ls-files"],
            capture_output=True,
            text=True,
            check=False,
        )
        if proc.returncode == 0:
            for line in proc.stdout.splitlines():
                if not line:
                    continue
                p = repo_root / line
                if p.is_file():
                    seen.add(p)
                    yield p

    for dirpath, dirnames, filenames in os.walk(repo_root):
        rel_dir = Path(dirpath).relative_to(repo_root)
        dirnames[:] = sorted(
            d
            for d in dirnames
            if d not in SKIP_DIRS
            and not (rel_dir == Path("fuzz") and d in ("corpus", "artifacts"))
        )
        for fname in sorted(filenames):
            if fname == ".DS_Store":
                continue
            p = Path(dirpath) / fname
            if p in seen:
                continue
            seen.add(p)
            yield p


def check_repository(repo_root: Path) -> List[str]:
    errors: List[str] = []

    for rel in FORBIDDEN_REL_PATHS:
        if (repo_root / rel).exists():
            errors.append(f"{rel}: forbidden artifact/legacy path present in repository")

    for pattern in FORBIDDEN_GLOB_PATTERNS:
        for hit in sorted(repo_root.glob(pattern)):
            rel = hit.relative_to(repo_root).as_posix()
            errors.append(f"{rel}: forbidden agent script present in repository")

    for path in iter_candidate_files(repo_root):
        rel = path.relative_to(repo_root).as_posix()
        if rel == SELF_REL or rel.startswith("history/"):
            continue
        for rule_name, pat in JARGON_RULES:
            if pat.search(rel):
                errors.append(f"{rel}:0: [{rule_name}] banned jargon in file path")
        if path.suffix.lower() in BINARY_SUFFIXES:
            continue
        try:
            text = path.read_text(encoding="utf-8")
        except UnicodeDecodeError:
            continue
        for lineno, rule_name, snippet in scan_text(rel, text):
            if lineno == 0:
                continue
            errors.append(f"{rel}:{lineno}: [{rule_name}] {snippet}")

    return errors


def run_self_test() -> None:
    positive_cases: Sequence[Tuple[str, str, str]] = (
        ("README.md", "branch unified-stage2 leaked", "unified-stage"),
        ("crates/qsag-agg/src/recursive.rs", 'let m = b"stage2-quintic-hierarchy";', "stage2-quintic"),
        ("validation/tests/foo.rs", "fn wave_x5_campaign() {}", "wave_x"),
        ("validation/tests/foo.rs", 'b"wave-x5-hqm2-shared"', "wave-x"),
        ("crates/qsag-accel/tests/t.rs", 'format!("e12_mut_spv_{}", id)', "e12_"),
        ("crates/qsag-core/src/pcg_dense.rs", "fn test_bounds_p1_06() {}", "p1_06"),
        ("lean/Qsag/Tests/CredentialsTeeth.lean", "/-- BACKLOG-57 tooth -/", "BACKLOG-"),
        ("hardware/ass2/pcb/REPORT.md", "../fable-fb7-datasheet/foo.typ", "fable-"),
        ("docs/README.md", "generated by claude-fable lane", "claude-fable"),
        ("hardware/ass2/run.sh", "bash astra_rx.sh", "astra_"),
        ("crates/qsag-quorum/src/cnf_party.rs", 'b"qsag-subcarbon-q1"', "subcarbon"),
        ("lean/Qsag/Exec/Tactic/SimulationKit.lean", "structure RetiredUnpackedCounter where", "RetiredUnpackedCounter"),
        ("crates/qsag-migrate/src/classical.rs", "pub enum LegacyCommitmentKind {}", "LegacyCommitmentKind"),
        ("crates/qsag-migrate/src/classical.rs", "pub struct LegacyOwnershipWitness {}", "LegacyOwnershipWitness"),
        ("crates/qsag-agg/README.md", "uses GoldilocksExt4 field", "GoldilocksExt4"),
        ("paper/qsag.typ", "WhirSecurityRegime tags 4..10", "WhirSecurityRegime"),
        ("docs/PERFORMANCE.md", "default BciksJohnsonQrom128 profile", "BciksJohnson"),
        ("crates/qsag-agg/src/recursive.rs", "struct SuccinctHierarchicalHemAggregate;", "SuccinctHierarchicalHemAggregate"),
        ("crates/qsag-agg/src/lib.rs", "match n { MergeNode::Branch(l, r) => {} }", "MergeNode::Branch"),
        ("paper/qsag.typ", "0-DRC Nangate45 route", "Nangate45"),
        ("ASSURANCE.md", "mapped on ASAP7 7 nm", "ASAP7"),
        ("README.md", "Dregg-180 5 V enclave", "Dregg-180"),
        ("hardware/asic/synth/RESULTS.md", "Nangate45 achieved 100 MHz signoff", "Nangate45"),
        ("docs/PERFORMANCE.md", "QSAG_BENCH_REGIME=4 CARGO_PROFILE_RELEASE_CODEGEN_UNITS=16", "QSAG_BENCH_REGIME"),
        ("docs/PERFORMANCE.md", "Run the benchmark on bb2 or hbox", "internal-hostname"),
        ("hardware/asic/verify.sh", 'SWARM_MEM_MAX=8G swarm-build "$@"' , "swarm-build-jargon"),
        ("hardware/ass2/lec/verify_enclave.sh", "cd /home/build/p-ass2-lane2 && verify_lane2.sh", "internal-lane-worktree"),
        ("crates/qsag-migrate/src/hem/zcash/mod.rs", 'HEM_ZCASH statement="x" regime=4 rows=1', "v1-regime-4"),
    )

    for rel, sample, expected_rule in positive_cases:
        hits = scan_text(rel, sample)
        matched_rules = {r for _, r, _ in hits}
        if expected_rule not in matched_rules:
            raise AssertionError(
                f"self-test failed: expected `{expected_rule}` on ({rel!r}, {sample!r}), got {hits}"
            )

    negative_cases: Sequence[Tuple[str, str]] = (
        ("crates/qsag-accel/src/vulkan.rs", "// Wave32 subgroup barrier noninterference"),
        ("crates/qsag-quorum/src/dzk.rs", 'const TAG: &[u8] = b"QSAG-WAVE-1-BARRIER";'),
        ("crates/qsag-ass2/src/vm.rs", "StepOutcome::Retired => count += 1,"),
        ("lean/Qsag/Protocol/Aggregation/Whir.lean", "def deployed_stage1_queries : Nat := 267"),
        ("hardware/fpga/rtl/qsag_mul64_dsp.sv", "// Align with Stage-2 DSP pipeline register"),
        ("crates/qsag-agg/src/zk_hem/relation.rs", "let st = sponge12_native(&msg);"),
        ("lean/Qsag/Protocol/Threshold/ThresholdMpc.lean", "theorem sumToprfState12_lanes : True := trivial"),
        ("crates/qsag-accel/src/poseidon2.rs", "const RC: u64 = 0x9FFB5BDA660B1D57;"),
        ("lean/Qsag/Protocol/Threshold/LatticePreprocessingFull.lean", "theorem t (hBox : x = y) : x = y := hBox"),
        ("lean/Qsag/Oracle/Spn.lean", "/-- Regime 1 on the full lists, deployed mixing constants -/"),
        ("history/SCP_CATALOG.md", "Archived Dregg-180, Nangate45, ASAP7, GoldilocksExt4, wave-x5."),
        (
            "hardware/asic/synth/RESULTS.md",
            "> **Library note:** `IHP SG13G2` and `Sky130 HD` are the manufacturable 130 nm foundry targets. `Nangate45` (`FreePDK45`) and `ASAP7` are purposely non-manufacturable academic reference libraries and are excluded from foundry signoff.",
        ),
        ("lean/Qsag/Protocol/Aggregation/Aggregation.lean", "abbrev F := GoldilocksExt4"),
    )

    for rel, sample in negative_cases:
        hits = scan_text(rel, sample)
        if hits:
            raise AssertionError(
                f"self-test false positive on ({rel!r}, {sample!r}): {hits}"
            )


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--root",
        type=Path,
        default=ROOT,
        help="Repository root to scan (default: parent of scripts/).",
    )
    parser.add_argument(
        "--self-test",
        action="store_true",
        help="Run built-in positive and negative regex/allowlist self-tests.",
    )
    args = parser.parse_args(argv)

    if args.self_test:
        run_self_test()
        print(
            f"SELF-TEST PASS: all {len(positive_cases) if False else 28} positive traps and 13 domain-preservation controls verified."
        )
        return 0

    run_self_test()
    repo_root = args.root.resolve()
    errors = check_repository(repo_root)
    if errors:
        for err in errors[:200]:
            print(f"HYGIENE_FAIL: {err}", file=sys.stderr)
        if len(errors) > 200:
            print(f"... ({len(errors) - 200} additional violations omitted)", file=sys.stderr)
        print(f"FAIL: {len(errors)} repository hygiene violations detected.", file=sys.stderr)
        return 1

    print(f"PASS: 0 hygiene or buried-identifier violations under {repo_root}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
