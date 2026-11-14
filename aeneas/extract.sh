#!/usr/bin/env bash
# Reproducible end-to-end Rust MIR -> Charon (.llbc) -> Aeneas (Lean 4) -> Lake verification script.
# Run on a Linux verification host with Charon, Aeneas, Rust, Lean, and Python 3 installed.
# Optionally set AENEAS_TOOLS_DIR to the directory containing Charon and Aeneas.
set -euo pipefail

if [[ "$(uname -s)" != Linux ]]; then
  echo "ERROR: extraction and verification must run on the designated Linux build host." >&2
  exit 1
fi

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
CRATE_DIR="${SCRIPT_DIR}/qsag-verified"
LEAN_DIR="${SCRIPT_DIR}/lean"
LLBC_FILE="${SCRIPT_DIR}/qsag_verified.llbc"

if [[ -d "${HOME}/.cargo/bin" ]]; then
  export PATH="${HOME}/.cargo/bin:${PATH}"
fi
if [[ -d "${HOME}/.elan/bin" ]]; then
  export PATH="${HOME}/.elan/bin:${PATH}"
fi

if [[ -n "${AENEAS_TOOLS_DIR:-}" && -d "${AENEAS_TOOLS_DIR}" ]]; then
  export PATH="${AENEAS_TOOLS_DIR}:${PATH}"
fi
for tool in charon aeneas; do
  if ! command -v "${tool}" >/dev/null 2>&1; then
    echo "ERROR: ${tool} is missing; install it on PATH or set AENEAS_TOOLS_DIR to its directory." >&2
    exit 1
  fi
done

echo "[1/4] Running Rust KAT, adversarial security, and qsag-core differential parity tests..."
(
  cd "${CRATE_DIR}"
  cargo test -- --nocapture
)

echo "[2/4] Extracting Rustc MIR to LLBC via Charon..."
(
  cd "${CRATE_DIR}"
  charon cargo --preset=aeneas --dest-file "${LLBC_FILE}" -- --lib
)

echo "[3/4] Translating LLBC to pure Lean 4.35 via Aeneas..."
(
  cd "${SCRIPT_DIR}"
  aeneas -sequential -backend lean -split-files -dest "${LEAN_DIR}" -subdir QsagVerified -no-progress-bar "${LLBC_FILE}"
)

for external in "${LEAN_DIR}/QsagVerified/FunsExternal.lean" "${LEAN_DIR}/QsagVerified/TypesExternal.lean"; do
  if [[ -e "${external}" ]]; then
    echo "ERROR: extraction produced an external-model dependency: ${external}" >&2
    exit 1
  fi
done

# Normalize generated headers for Lean 4.35's module system. Idempotent when
# Aeneas already emits module/public imports; preserve the generated body.
python3 - "${LEAN_DIR}/QsagVerified" <<'PY_HEADERS'
from pathlib import Path
import re
import sys

for name in ("Types.lean", "Funs.lean"):
    path = Path(sys.argv[1]) / name
    lines = path.read_text().splitlines(keepends=True)
    # Only inspect the generated header, before the first open/namespace command.
    boundary = next((i for i, line in enumerate(lines)
                     if line.startswith(("open ", "namespace ", "set_option "))), None)
    if boundary is None:
        raise SystemExit(f"Cannot identify generated header in {path}")
    header, body = lines[:boundary], lines[boundary:]
    imports = []
    comments = []
    for line in header:
        stripped = line.strip()
        match = re.fullmatch(r"(?:public\s+)?import\s+(.+)", stripped)
        if match:
            if match[1] not in imports:
                imports.append(match[1])
        elif stripped in ("module", "@[expose] public section", "public section"):
            continue
        elif not stripped or stripped.startswith("--"):
            comments.append(line)
        else:
            raise SystemExit(f"Unexpected generated header in {path}: {stripped}")
    if not imports:
        raise SystemExit(f"Missing generated imports in {path}")
    path.write_text("".join(comments) + "module\n"
                    + "".join(f"public import {module}\n" for module in imports)
                    + "@[expose] public section\n" + "".join(body))
PY_HEADERS

echo "[4/4] Verifying Aeneas prelude, extracted MIR functions, and 0-sorry refinement theorems via Lake..."
(
  cd "${LEAN_DIR}"
  lake build
  lake build QsagVerifiedChallenge AuditMirAxioms
  test -s lake-manifest.json
)

echo "SUCCESS: Charon + Aeneas extraction and Lean 4 machine-checked proofs verified cleanly."
