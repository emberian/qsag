#!/usr/bin/env bash
set -eo pipefail
[[ -z "${QSAG_ENV_SCRIPT:-}" ]] || source "$QSAG_ENV_SCRIPT"
set -u
cd "$(dirname "$0")"

nl_path=${1:?Usage: ./run_postroute_gl.sh /path/to/final/nl/chip_top.nl.v [/path/to/mapped.v]}
gold_mapped=${2:-../synth/out/gf180/mapped.v}
chip_top_sv=${3:-../../pnr/src/chip_top.sv}
label="postroute_$(basename "$(dirname "$(dirname "$nl_path")")")"
out="$PWD/build/$label"
mkdir -p "$out" logs
exec > >(tee "logs/$label.log") 2>&1

pdk=${PDK_REF:-${PDK_ROOT:-/opt/pdk}/gf180mcuD/libs.ref}
scdir="$pdk/gf180mcu_fd_sc_mcu7t5v0/verilog"
cells="$scdir/gf180mcu_fd_sc_mcu7t5v0.v"
ram="$pdk/gf180mcu_fd_ip_sram/verilog/gf180mcu_fd_ip_sram__sram512x8m8wm1.v"
io_v="$pdk/gf180mcu_fd_io/verilog/gf180mcu_fd_io.v"
io_bb="$pdk/gf180mcu_fd_io/verilog/gf180mcu_fd_io__blackbox.v"

sha256sum "$nl_path" "$gold_mapped" "$cells" "$ram" "$io_v"
python3 prepare_postroute.py "$cells" "$nl_path" "$out" "$ram" "$io_v"

echo "=== [1/2] Post-Route Formal Equivalence Check (Yosys equiv: gold chip_top+mapped.v vs final/nl/chip_top.nl.v) ==="
cat > "$out/sram_bb.v" <<'SRAM_BB'
(* blackbox *)
module gf180mcu_fd_ip_sram__sram512x8m8wm1 (
    input wire CLK, CEN, GWEN,
    input wire [7:0] WEN,
    input wire [8:0] A,
    input wire [7:0] D,
    output wire [7:0] Q
);
endmodule
SRAM_BB
cat > "$out/postroute_lec.ys" <<YS
read_verilog -lib "$out/sram_bb.v"
read_verilog -lib "$io_bb"
read_verilog "$scdir/primitives.v" "$cells"
read_verilog -sv -DSLOT_0P5X0P5 -DPAD_gf180mcu_fd_io "$chip_top_sv" "$gold_mapped"
hierarchy -top chip_top
delete t:gf180mcu_fd_io__dvdd t:gf180mcu_fd_io__dvss t:gf180mcu_fd_io__asig_5p0 t:gf180mcu_ws_ip__*
flatten
opt_clean -purge
design -stash gold

read_verilog -lib "$out/sram_bb.v"
read_verilog -lib "$io_bb"
read_verilog "$scdir/primitives.v" "$cells"
read_verilog "$out/chip_top_func.nl.v"
hierarchy -top chip_top
flatten
opt_clean -purge
design -stash gate

design -copy-from gold -as gold chip_top
design -copy-from gate -as gate chip_top
equiv_make gold gate equiv
equiv_simple -seq 2
equiv_induct -seq 2
equiv_status -assert
YS
yosys -Q -s "$out/postroute_lec.ys" -l "$out/postroute_lec.log"
tail -n 20 "$out/postroute_lec.log"

echo "=== [2/2] Post-Route 4-State Icarus -gspecify Simulation on final/nl/chip_top.nl.v ==="
iverilog -g2012 -gspecify -Ttyp -s tb_postroute -I"$out" \
    "$scdir/primitives.v" "$out/timed.v" "$out/sram.v" "$out/io_pads.v" \
    "$out/chip_top_func.nl.v" tb_postroute.sv \
    -o "$out/postroute.vvp" 2>"logs/$label.compile.log" || { tail -40 "logs/$label.compile.log"; exit 1; }
stdbuf -oL vvp "$out/postroute.vvp"
