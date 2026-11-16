#!/bin/sh
# Generate the test scripts from the golden model (remote, cwd = project root).
set -e
mkdir -p build
python3 tb/gen_script.py tb/fixtures/lean_external_oracle_vectors.json build/script_full.txt
python3 tb/gen_script.py tb/fixtures/lean_external_oracle_vectors.json build/script_quick.txt quick
