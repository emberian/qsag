#!/usr/bin/env bash
# Report GF180 standard-cell area, with SRAM instances checked before mapping.
set -euo pipefail
cd "$(dirname "$0")/.."
[[ $(uname -s) == Linux ]]
export TMPDIR="$PWD/tmp"
work=$(mktemp -d "$TMPDIR/ass2-area.XXXXXXXX")
trap 'rm -rf "$work"' EXIT
lib=pdk/gf180mcu_fd_sc_mcu7t5v0__tt_025C_5v00.lib
rtl=(rtl/qsag_ass2_pkg.sv)
for f in rtl/*.sv; do [[ $f == "${rtl[0]}" ]] || rtl+=("$f"); done
cat > "$work/area.abc" <<'ABC'
strash
balance
rewrite
balance
&get -n
&dch -f
&nf -a
&put
ABC
yosys -V
for top in qsag_ass2_keccak qsag_ass2_gf_step qsag_gl64_karatsuba_csa qsag_ass2_enclave_top; do
    macros=''
    if [[ $top == qsag_ass2_enclave_top ]]; then
        macros='select -assert-count 16 t:gf180mcu_fd_ip_sram__sram512x8m8wm1'
    fi
    cat > "$work/map.ys" <<YS
read_slang --top $top -DGF180_SRAM_MACRO ${rtl[*]}
design -save extracted
proc
opt
select -assert-none t:\$mul
design -load extracted
synth -top $top -noabc
$macros
dfflibmap -liberty $lib
abc -script $work/area.abc -liberty $lib
stat -liberty $lib
YS
    yosys -Q -m slang -s "$work/map.ys" > "$work/map.log"
    rg 'Chip area|of which used for sequential elements|^ +16 +- +gf180mcu_fd_ip_sram' "$work/map.log"
done
