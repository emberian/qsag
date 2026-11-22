#!/usr/bin/env bash
set -euo pipefail
[[ $(uname -s) == Linux ]] || { echo "Run on bb2" >&2; exit 2; }
here=$(cd "$(dirname "$0")" && pwd)
rtl=$(cd "$here/../rtl" && pwd)
export PATH="/home/build/qsag-ni-asic/tools/oss-cad-suite/bin:$PATH"
work=$(mktemp -d "${TMPDIR:-/tmp}/ass2-verilator.XXXXXXXX")
trap 'rm -rf "$work"' EXIT
source "$here/../synth/rtl_sources.sh"
if [[ $# == 0 ]]; then
    vectors="$work/suite.vec"
    firmware=()
    for name in canopy cth jive sumcheck; do
        firmware+=(--firmware "$here/firmware_kats/$name.bin")
    done
    python3 "$here/ass2_model.py"
    python3 "$here/gen_cosim_vectors.py" "$vectors" "${firmware[@]}"
else
    vectors=$1
fi
# Lint the production core on its own; the simulation wrapper intentionally
# leaves unused debug outputs open.
lint_top=qsag_ass2_core
[[ ! -f "$rtl/qsag_ass2_enclave_top.sv" ]] || lint_top=qsag_ass2_enclave_top
verilator -DASS2_FAST_ENTROPY --lint-only -Wall --top-module "$lint_top" -I"$rtl" "${rtl_sources[@]}"
verilator -DASS2_FAST_ENTROPY --cc --exe --build -j "${JOBS:-4}" --Mdir "$work/obj_dir" \
    --top-module ass2_cosim_top -I"$rtl" "${rtl_sources[@]}" \
    "$here/ass2_cosim_top.sv" "$here/sim_ass2_lockstep.cpp"
"$work/obj_dir/Vass2_cosim_top" "$vectors"
