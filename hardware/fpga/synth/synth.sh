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
    ecp5) tile="-chparam AW 16 -chparam BW 16"; cmd="synth_ecp5 -top $top" ;;
    *) echo "family must be xcup or ecp5"; exit 2 ;;
esac
case "$top" in
    qsag_keccak_turboshake|qsag_gf128_clmul|qsag_gl64_reduce|qsag_p2_linear|qsag_p2_chain_engine|qsag_sdp_bram|qsag_gf128_reduce|qsag_clmul_kara) tile="" ;;
esac
json=""; [ "${WRITE_JSON:-0}" = 1 ] && json="write_json $out.json;"
yosys -l "$out.log" -q -p "read_verilog -sv $SRC; hierarchy -top $top $tile $chparam; $cmd; $json tee -o $out.stat stat -top $top; tee -o $out.ltp ltp -noff" \
    > /dev/null
python3 synth/summarize.py "$out.stat" "$out.ltp" "$fam" "$tag" | tee "$out.summary"
