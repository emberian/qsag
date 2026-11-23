#!/usr/bin/env bash
# Run on a Linux host from hardware/asic (or set QSAG_WORK_DIR).
set -euo pipefail
cd "$(dirname "$0")"
[[ "$(uname -s)" == Linux && "$PWD" == "${QSAG_WORK_DIR:-$PWD}" ]]
export TMPDIR="${TMPDIR:-$PWD/work_tmp}"
mkdir -p "$TMPDIR" logs vec
run() { "$@"; }

case "${1:?select vectors, sim, live, reference, formal, or area}" in
  vectors)
    run python3 gen/gen_vectors.py fixtures/lean_external_oracle_vectors.json vec
    python3 tb/rust/prepare.py rust-unified
    (cd rust-unified && run cargo build --release -j2 -p qsag-agg --example qsag_ni_kat --example qsag_ni_live)
    rust-unified/target/release/examples/qsag_ni_kat vec/trace_v2.hex ;;
  sim)
    export PATH="$PWD/toolchain/nov/oss-cad-suite/bin:$PATH"
    run bash tb/run.sh lint 2>&1 | tee logs/lint_final.log
    for top in tb_units tb_top tb_zkhem_v2_top; do run bash tb/run.sh "$top"; done ;;
  live) run bash tb/rust/live.sh ;;
  reference)
    # rust-pristine is a second, untouched copy of the software input tree.
    cp tb/rust/reference.rs rust-pristine/crates/qsag-agg/examples/qsag_ni_reference.rs
    cp tb/rust/proof_fixture.rs rust-pristine/crates/qsag-agg/examples/
    (cd rust-pristine && run cargo build -j2 --release -p qsag-agg --example qsag_ni_reference)
    run rust-pristine/target/release/examples/qsag_ni_reference vec/proof_v2.bin | tee logs/reference.log ;;
  formal)
    export PATH="$PWD/toolchain/oss-cad-suite/bin:$PATH"
    run bash lec/addsub.sh 2>&1 | tee logs/addsub_miter.log
    for block in fp5 shared; do run python3 lec/miter.py "$block" | tee "logs/${block}_miter.log"; done ;;
  area)
    export PATH="$PWD/toolchain/oss-cad-suite/bin:$PATH"
    export LIBERTY="${LIBERTY:-$PWD/toolchain/sg13g2_stdcell_typ_1p20V_25C.lib}"
    CAP=10G run bash synth/area.sh baseline baseline
    CAP=10G run bash synth/area.sh . final
    python3 synth/compare.py logs/area_baseline.stat logs/area_final.stat | tee logs/area_delta.log ;;
  *) exit 2 ;;
esac
