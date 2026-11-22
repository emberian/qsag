#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
rtl=$(cd "$here/../rtl" && pwd)
source "$here/../synth/rtl_sources.sh"
sc="${PDK_REF:?Set PDK_REF to GF180MCU-C libs.ref}/gf180mcu_fd_sc_mcu7t5v0/verilog"
verilator --lint-only -Wall -DFUNCTIONAL --top-module qsag_ass2_enclave_top \
  "$here/physical_ro.vlt" -v "$sc/gf180mcu_fd_sc_mcu7t5v0.v" -v "$sc/primitives.v" \
  "${rtl_sources[@]}"
