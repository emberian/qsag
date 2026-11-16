#!/usr/bin/env bash
# Yosys synthesis of one QSAG-NI module for one FPGA family. Run on a build box:
#   synth.sh <xcup|ecp5> <top module> [tag] [-chparam NAME VALUE ...]
# xcup : synth_xilinx -family xcup  (UltraScale+: LUT6, FDRE, CARRY8, DSP48E2, RAMB36E2)
# ecp5 : synth_ecp5                 (LUT4, TRELLIS_FF, CCU2C, MULT18X18D, DP16KD)
# The hierarchy is kept (each module is synthesised once and counted by instance) so the big
# tops finish inside one 600 s build slot; reports land in build/synth/<tag>.<family>.{log,stat,json}.
set -euo pipefail
cd "$(dirname "$0")/.."
fam="$1"; top="$2"; tag="${3:-$top}"; shift; shift; [ $# -gt 0 ] && shift
chparam="$*"
mkdir -p build/synth
SRC="$(tr '\n' ' ' < synth/srcs.txt)"
out="build/synth/$tag.$fam"
# Multiplier tiling per family: 26x17 on DSP48E2, 16x16 on MULT18X18D.
case "$fam" in
    xcup) tile="-chparam AW 26 -chparam BW 17"; cmd="synth_xilinx -family xcup -top $top -noiopad" ;;
    ecp5) tile="-chparam AW 16 -chparam BW 16"; cmd="synth_ecp5 -top $top ${ECP5_FLAT:--noflatten}" ;;
    *) echo "family must be xcup or ecp5"; exit 2 ;;
esac
case "$top" in
    qsag_keccak_turboshake|qsag_gf128_clmul|qsag_gl64_reduce|qsag_p2_linear|qsag_p2_chain_engine|qsag_sdp_bram|qsag_gf128_reduce|qsag_clmul_kara) tile="" ;;
esac
json=""; [ "${WRITE_JSON:-0}" = 1 ] && json="write_json $out.json;"
# Logic depth: delete every sequential / hard cell, then the longest remaining path in any module
# is the longest register-to-register run of LUTs and carry elements.
SEQ="t:FDRE t:FDSE t:FDCE t:FDPE t:SRL16E t:SRLC32E t:DSP48E2 t:RAMB36E2 t:RAMB18E2 t:RAM32M t:RAM64M t:RAM32X1D t:RAM64X1D t:RAM32M16 t:RAM64M8 t:BUFG t:TRELLIS_FF t:MULT18X18D t:DP16KD t:TRELLIS_DPR16X4"
yosys -l "$out.log" -q -p "read_verilog -sv $SRC; hierarchy -top $top $tile $chparam; $cmd; $json tee -o $out.stat stat -top $top; delete $SEQ; tee -o $out.ltp ltp" \
    > /dev/null
python3 synth/summarize.py "$out.stat" "$out.ltp" "$fam" "$tag" | tee "$out.summary"
