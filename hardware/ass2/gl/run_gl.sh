#!/usr/bin/env bash
set -eo pipefail
[[ -z "${QSAG_ENV_SCRIPT:-}" ]] || source "$QSAG_ENV_SCRIPT"
set -u
cd "$(dirname "$0")"
mapdir=${1:-../synth/results/gf180}
label=${2:-$(basename "$mapdir")}
out="$PWD/build/$label"
mkdir -p "$out" logs
exec > >(tee "logs/$label.log") 2>&1
pdk=${PDK_REF:-${PDK_ROOT:-/opt/pdk}/gf180mcuD/libs.ref}
scdir="$pdk/gf180mcu_fd_sc_mcu7t5v0/verilog"
cells="$scdir/gf180mcu_fd_sc_mcu7t5v0.v"
ram="$pdk/gf180mcu_fd_ip_sram/verilog/gf180mcu_fd_ip_sram__sram512x8m8wm1.v"
mapped="$mapdir/mapped.v"
if [[ ! -f "$mapped" ]]; then
    gzip -dc "$mapped.gz" > "$out/mapped.v"
    mapped="$out/mapped.v"
fi
if [[ -e "$mapdir/mapped.sha256" ]]; then
    [[ $(sha256sum "$mapped" | cut -d' ' -f1) == "$(cat "$mapdir/mapped.sha256")" ]] ||
        { echo "Netlist checksum mismatch"; exit 1; }
fi
iverilog -V 2>&1 | sed -n '1p'
sha256sum "$mapped" "$mapdir/standard_cells.stat" "$cells" "$scdir/primitives.v" "$ram"
python3 prepare.py "$cells" "$mapped" "$mapdir/standard_cells.stat" "$out" "$ram"
echo "Compiling iverilog -g2012 -gspecify -Ttyp -s tb"
iverilog -g2012 -gspecify -Ttyp -s tb -I"$out" \
    "$scdir/primitives.v" "$out/timed.v" "$out/sram.v" "$mapped" tb.sv \
    -o "$out/test.vvp" 2>"logs/$label.compile.log" || { tail -40 "logs/$label.compile.log"; exit 1; }
stdbuf -oL vvp "$out/test.vvp"
