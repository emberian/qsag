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
CRATE_DIR="${SCRIPT_DIR}/qsag-whir-verified"
LEAN_DIR="${SCRIPT_DIR}/lean-whir"
mkdir -p "${LEAN_DIR}/.lake"
EXTRACT_DIR="$(mktemp -d "${LEAN_DIR}/.lake/whir-extract.XXXXXXXX")"
export TMPDIR="${EXTRACT_DIR}"
LLBC_FILE="${EXTRACT_DIR}/qsag_whir_verified.llbc"
LOCK="$(dirname "$(dirname "${SCRIPT_DIR}")")/cargo.lock"

rust_build() {
  flock "${LOCK}" "$@"
}

cleanup() {
  rm -rf -- "${EXTRACT_DIR}"
}
trap cleanup EXIT

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

echo "[1/5] Running standalone Rust boundary tests..."
(
  cd "${CRATE_DIR}"
  rust_build cargo test --release -p qsag-whir-verified
)

echo "[2/5] Extracting Rustc MIR to LLBC via Charon..."
(
  cd "${CRATE_DIR}"
  rust_build charon cargo --preset=aeneas --dest-file "${LLBC_FILE}" -- --lib
)

echo "[3/5] Translating LLBC to pure Lean 4.35 via Aeneas..."
(
  cd "${SCRIPT_DIR}"
  aeneas -sequential -backend lean -split-files -dest "${EXTRACT_DIR}" -subdir QsagWhirVerified -no-progress-bar "${LLBC_FILE}"
)

shopt -s nullglob
externals=("${EXTRACT_DIR}/QsagWhirVerified/"*External*.lean)
if (( ${#externals[@]} )); then
  echo "ERROR: extraction produced external declarations: ${externals[*]}" >&2
  exit 1
fi

# Normalize generated headers for Lean 4.35's module system without file-wide @[expose].
python3 - "${EXTRACT_DIR}/QsagWhirVerified" <<'PY_HEADERS'
from pathlib import Path
import re
import sys

for name in ("Types.lean", "Funs.lean"):
    path = Path(sys.argv[1]) / name
    lines = path.read_text().splitlines(keepends=True)
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
    body_text = "".join(body)
    if name == "Funs.lean":
        # Publish kernel-checked equations rather than importing private bodies in clients.
        imports.append("Qsag.Tactic.AssuranceKit")
        definitions = re.findall(r"(?m)^(?:@\[[^]]*\]\s*)?def\s+([A-Za-z_][A-Za-z0-9_'.]*)", body_text)
        if len(definitions) != 86 or len(set(definitions)) != 86:
            raise SystemExit("Unexpected WHIR extraction API inventory")
        body_text += ("\npublic section\n#export_eqns " +
                      " ".join("qsag_whir_verified." + n for n in definitions) + "\nend\n")
    path.write_text("".join(comments) + "module\n"
                    + "".join(f"public import {module}\n" for module in imports)
                    + "public section\n" + body_text)
PY_HEADERS

for name in Types Funs; do
  cp "${EXTRACT_DIR}/QsagWhirVerified/${name}.lean" "${LEAN_DIR}/QsagWhirVerified/${name}.lean"
done

if [[ "${1:-}" == "--extract-only" ]]; then
  exit 0
fi

echo "[4/5] Verifying Aeneas prelude, extracted MIR functions, and refinement theorems via Lake..."
(
  cd "${LEAN_DIR}"
  lake build --wfail
  lake exe audit-whir-mir-axioms
  test -s lake-manifest.json
)

echo "[5/5] Checking production linkage, hierarchical composition, and lint policy..."
(
  cd "${SCRIPT_DIR}/.."
  rust_build cargo test --release -p qsag-agg --lib extracted_quintic_whir_kernels_match_production_fp5_and_canopy
  rust_build cargo test --release -p qsag-agg --lib zk_hem::v2::pcs::tests
  rust_build cargo test --release -p qsag-agg --lib hem_quintic
  rust_build cargo test --release -p qsag-agg --lib recursive::tests
  rust_build cargo clippy -p qsag-agg --all-targets -- -D warnings
  rust_build cargo check -p qsag-agg --no-default-features
)

python3 "${SCRIPT_DIR}/../scripts/check_extraction_provenance.py" --record --crate qsag-whir-verified

echo "SUCCESS: Charon + Aeneas extraction and Lean 4 machine-checked proofs verified cleanly."
