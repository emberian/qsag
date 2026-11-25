#!/usr/bin/env python3
"""Replay MIR challenges with the path dependency inside the comparator sandbox.

Run on a Linux build host after building both Lean packages. Source and warm
artifacts are copied into an isolated temporary package; only dependency paths
in that copy change. The default comparator sandbox remains enabled.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import tomllib


def prepare_snapshot(package: Path, destination: Path) -> str:
    config = tomllib.loads((package / "lakefile.toml").read_text())
    requirements = config.get("require", [])
    if len(requirements) != 1 or requirements[0].get("name") != "qsag":
        raise ValueError("Expected exactly the local qsag dependency")
    dependency = (package / requirements[0]["path"]).resolve(strict=True)
    if dependency != (package.parent.parent / "lean").resolve(strict=True):
        raise ValueError("qsag dependency must be the repository's main Lean package")
    for root in (package, dependency):
        if not (root / ".lake/build/lib/lean").is_dir():
            raise ValueError(f"Build the Lean package before replay: {root}")
    digest = hashlib.sha256()
    for label, root in (("mir", package), ("qsag", dependency)):
        for source in sorted(root.rglob("*.lean")):
            if ".lake" in source.relative_to(root).parts:
                continue
            digest.update(f"{label}/{source.relative_to(root)}\0".encode())
            digest.update(source.read_bytes())
            digest.update(b"\0")
    ignore = shutil.ignore_patterns(".git", "__pycache__", "target")
    shutil.copytree(package, destination, ignore=ignore, symlinks=True)
    shutil.copytree(dependency, destination / "vendor/qsag", ignore=ignore, symlinks=True)
    config_path = destination / "lakefile.toml"
    original = config_path.read_text()
    old_path = requirements[0]["path"]
    needle = f'path = "{old_path}"'
    if original.count(needle) != 1:
        raise ValueError("Ambiguous qsag path in Lake configuration")
    config_path.write_text(original.replace(needle, 'path = "vendor/qsag"'))
    manifest_path = destination / "lake-manifest.json"
    manifest = json.loads(manifest_path.read_text())
    entries = [p for p in manifest["packages"] if p["name"] == "qsag"]
    if len(entries) != 1 or entries[0]["type"] != "path":
        raise ValueError("Expected one path dependency in the Lake manifest")
    entries[0]["dir"] = "vendor/qsag"
    manifest_path.write_text(json.dumps(manifest, indent=2) + "\n")
    return digest.hexdigest()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--package", type=Path,
                        default=Path(__file__).resolve().parents[1] / "aeneas/lean")
    args = parser.parse_args()
    if sys.platform != "linux":
        parser.error("Comparator replay must run on a designated Linux build host")
    package = args.package.resolve(strict=True)
    with tempfile.TemporaryDirectory(prefix="qsag-comparator-") as scratch:
        snapshot = Path(scratch) / "project"
        fingerprint = prepare_snapshot(package, snapshot)
        print(f"MIR comparator source SHA-256: {fingerprint}", flush=True)
        print("Replaying the self-contained snapshot with the default sandbox", flush=True)
        return subprocess.run(["lake", "comparator", "--paranoid"], cwd=snapshot).returncode


if __name__ == "__main__":
    raise SystemExit(main())
