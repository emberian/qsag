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

# The only post-processing of generated Lean. Aeneas emits `module`, `public import`s and a
# file-wide `@[expose] public section`; this narrows the latter to `public section` and
# exposes exactly four scalar aliases. Everything else is byte-for-byte Aeneas output, and
# the provenance record binds the result. It is idempotent.
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
    # Scalar aliases must be transparent to Lean's compiler across module boundaries.
    # Expose only these aliases, never an entire generated section.
    body_text = "".join(body)
    if name == "Types.lean":
        for alias in ("goldilocks.Goldilocks", "tower.Gf256", "tower.Tower128", "tower.Gf16"):
            raw = f"@[reducible]\ndef {alias} :="
            exposed = f"@[reducible, expose]\ndef {alias} :="
            # A renamed or reshaped alias must stop the run, not pass through unexposed.
            if body_text.count(raw) + body_text.count(exposed) != 1:
                raise SystemExit(f"Expected exactly one scalar alias {alias} in {path}")
            body_text = body_text.replace(raw, exposed)
    path.write_text("".join(comments) + "module\n"
                    + "".join(f"public import {module}\n" for module in imports)
                    + "public section\n" + body_text)
PY_HEADERS

echo "[4/4] Verifying Aeneas prelude, extracted MIR functions, and 0-sorry refinement theorems via Lake..."
(
  cd "${LEAN_DIR}"
  python3 check_audit_coverage.py
  # Extraction, proofs, primitive welds and their axiom census. These need only the primitive
  # `Qsag` specifications.
  lake build --wfail Aeneas QsagVerified QsagMirProofs QsagSpecWeld AuditMirAxioms
  # Comparator challenge statements; their bodies are placeholders by design.
  lake build QsagVerifiedChallenge
  # Protocol-level welds; these need the whole `Qsag.MirSpecBridge` import cone.
  lake build --wfail QsagCustodyWeld
  # Runtime census over both import-all environments; exits non-zero on any axiom
  # outside {propext, Quot.sound}.
  lake exe audit-mir-axioms
  test -s lake-manifest.json
)

python3 "${SCRIPT_DIR}/../scripts/check_extraction_provenance.py" --record --crate qsag-verified

echo "SUCCESS: Charon + Aeneas extraction and Lean 4 machine-checked proofs verified cleanly."
