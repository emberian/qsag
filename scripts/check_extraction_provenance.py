#!/usr/bin/env python3
"""Bind successful extraction output to exact source, prelude and extractor binaries.

The extraction scripts record only after their build gates succeed. A digest check
establishes freshness relative to that recorded run, not correctness of extraction.
"""
import argparse
import hashlib
import json
from pathlib import Path
import platform
import shutil

ROOT = Path(__file__).resolve().parents[1]

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def inventory(crate):
    source = ROOT / "aeneas" / crate
    package = ROOT / "aeneas" / ("lean" if crate == "qsag-verified" else "lean-whir")
    module = "QsagVerified" if crate == "qsag-verified" else "QsagWhirVerified"
    files = list((source / "src").rglob("*.rs"))
    files += [p for p in (source / "Cargo.toml", source / "rust-toolchain.toml", source / "build.rs") if p.exists()]
    files += [package / module / f for f in ("Types.lean", "Funs.lean")]
    files += [package / "Aeneas.lean", *sorted((package / "Aeneas").rglob("*.lean"))]
    return {str(p.relative_to(ROOT)): digest(p) for p in sorted(files)}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--record", action="store_true")
    parser.add_argument("--crate", choices=("qsag-verified", "qsag-whir-verified"))
    args = parser.parse_args()
    for crate in ([args.crate] if args.crate else ["qsag-verified", "qsag-whir-verified"]):
        manifest = ROOT / "aeneas" / crate / "extraction-provenance.json"
        files = inventory(crate)
        if args.record:
            if platform.system() != "Linux":
                raise SystemExit("Recording requires a successful Linux extraction run")
            tools = {}
            for name in ("charon", "charon-driver", "aeneas"):
                path = shutil.which(name)
                if not path:
                    raise SystemExit(f"Missing extractor: {name}")
                tools[name] = digest(Path(path))
            manifest.write_text(json.dumps({"format": 1, "files": files, "extractor_sha256": tools}, indent=2, sort_keys=True) + "\n")
        else:
            expected = json.loads(manifest.read_text())["files"]
            changed = sorted(k for k in files.keys() | expected.keys() if files.get(k) != expected.get(k))
            if changed:
                raise SystemExit(f"{crate}: extraction provenance differs: " + ", ".join(changed))
        print(f"{crate}: exact extraction source/prelude/output binding PASS ({len(files)} files)")

if __name__ == "__main__":
    main()
