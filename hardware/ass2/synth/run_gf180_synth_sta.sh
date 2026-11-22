#!/usr/bin/env bash
set -eo pipefail
[[ $(uname -s) == Linux ]] || { echo "Run inside hbox:dregg180-astra" >&2; exit 2; }
source /work/wave-e5/dev_env.sh
set -u
here=$(cd "$(dirname "$0")" && pwd)
rtl=$(cd "$here/../rtl" && pwd)
top=qsag_ass2_enclave_top
[[ -s "$rtl/$top.sv" ]] || { echo "Missing $rtl/$top.sv" >&2; exit 2; }
mkdir -p "${OUT:-$here/out/gf180}"
cd "${OUT:-$here/out/gf180}"
pdk=${PDK_REF:-/var/tmp/deep3-ass2/pdk}
sc=gf180mcu_fd_sc_mcu7t5v0
ram=gf180mcu_fd_ip_sram__sram512x8m8wm1
map_corner=${MAP_CORNER:-ss_125C_4v50}
target_ps=${TARGET_PS:-22000}
lib="$pdk/$sc/lib/${sc}__${map_corner}.lib"
ram_lib="$pdk/gf180mcu_fd_ip_sram/lib/${ram}__${map_corner}.lib"
source "$here/rtl_sources.sh"
sha256sum "${rtl_sources[@]}" > rtl.sha256
printf '"%s"\n' "${rtl_sources[@]}" "$here/gf180_sram_blackbox.sv" > rtl.f
cat > abc.constr <<'CONSTR'
set_driving_cell gf180mcu_fd_sc_mcu7t5v0__buf_4
set_load 0.05
CONSTR
cat > synth.ys <<YS
read_slang --top $top -DGF180_SRAM_MACRO -DQSAG_EXTERNAL_SRAM_MODEL -I$rtl -f rtl.f
hierarchy -check -top $top
synth -flatten -noabc -top $top
techmap -map "$here/gf180_latches.v"
dfflibmap -liberty "$lib"
abc -liberty "$lib" -liberty "$ram_lib" -constr abc.constr -dont_use gf180mcu_fd_sc_mcu7t5v0__dlya_* -dont_use gf180mcu_fd_sc_mcu7t5v0__dlyb_* -dont_use gf180mcu_fd_sc_mcu7t5v0__dlyc_* -dont_use gf180mcu_fd_sc_mcu7t5v0__dlyd_* -D $target_ps
opt_clean -purge
hilomap -hicell gf180mcu_fd_sc_mcu7t5v0__tieh Z -locell gf180mcu_fd_sc_mcu7t5v0__tiel ZN
select -assert-count 2 t:$ram
select -assert-none t:\$*
tee -o standard_cells.stat stat -liberty "$lib"
write_verilog -noattr -noexpr -nohex -nodec mapped.v
YS
yosys -Q -s synth.ys -l synth.log > /dev/null
python3 "$here/buffer_resets.py" mapped.v
cat > census.ys <<YS
read_liberty -lib "$lib"
read_liberty -lib "$ram_lib"
read_verilog mapped.v
hierarchy -check -top $top
opt_clean -purge
select -assert-count 2 t:$ram
select -assert-none t:\$*
tee -o standard_cells.stat stat -liberty "$lib"
write_verilog -noattr -noexpr -nohex -nodec mapped.v
YS
yosys -Q -s census.ys -l census.log > /dev/null
sha256sum --check --status rtl.sha256
sha256sum mapped.v | cut -d' ' -f1 > mapped.sha256
for corner in ss_125C_4v50 tt_025C_5v00 ff_n40C_5v50; do
    export ASS2_SC_LIB="$pdk/$sc/lib/${sc}__${corner}.lib"
    export ASS2_RAM_LIB="$pdk/gf180mcu_fd_ip_sram/lib/${ram}__${corner}.lib"
    [[ -r "$ASS2_SC_LIB" && -r "$ASS2_RAM_LIB" ]]
    sta -exit "$here/gf180_sta.tcl" 2>&1 | tee "sta-$corner.log"
    if grep -Eq '^(Error:|Warning:.*(black box|not found))' "sta-$corner.log"; then exit 1; fi
done
cat standard_cells.stat
