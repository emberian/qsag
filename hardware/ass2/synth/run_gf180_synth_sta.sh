#!/usr/bin/env bash
set -eo pipefail
[[ $(uname -s) == Linux ]] || { echo "Run on a Linux host" >&2; exit 2; }
[[ -z "${QSAG_ENV_SCRIPT:-}" ]] || source "$QSAG_ENV_SCRIPT"
set -u
here=$(cd "$(dirname "$0")" && pwd)
rtl=$(cd "$here/../rtl" && pwd)
top=qsag_ass2_enclave_top
[[ -s "$rtl/$top.sv" ]] || { echo "Missing $rtl/$top.sv" >&2; exit 2; }
mkdir -p "${OUT:-$here/out/gf180}"
cd "${OUT:-$here/out/gf180}"
pdk=${PDK_REF:-${PDK_ROOT:-/opt/pdk}/gf180mcuD/libs.ref}
sc=gf180mcu_fd_sc_mcu7t5v0
ram=gf180mcu_fd_ip_sram__sram512x8m8wm1
map_corner=${MAP_CORNER:-ss_125C_4v50}
lib="$pdk/$sc/lib/${sc}__${map_corner}.lib"
ram_lib="$pdk/gf180mcu_fd_ip_sram/lib/${ram}__${map_corner}.lib"
source "$here/rtl_sources.sh"
sha256sum "${rtl_sources[@]}" > rtl.sha256
printf '"%s"\n' "${rtl_sources[@]}" "$here/gf180_sram_blackbox.sv" > rtl.f
cat > abc.constr <<'CONSTR'
set_driving_cell gf180mcu_fd_sc_mcu7t5v0__buf_4
set_load 0.05
CONSTR
cat > fast_add.abc <<'ABC_FAST'
strash; balance; map -D 5000; buffer -N 16; upsize -D 5000; stime -p
ABC_FAST
dont_use="-dont_use gf180mcu_fd_sc_mcu7t5v0__dly* -dont_use gf180mcu_fd_sc_mcu7t5v0__mux2_1 -dont_use gf180mcu_fd_sc_mcu7t5v0__oai33_2 -dont_use gf180mcu_fd_sc_mcu7t5v0__sdff*"
cat > area.abc <<'ABC'
fx; mfs; strash; drf -l; balance; drw -l; drw -z -l; balance; drf -z -l; drw -z -l; balance;
fraig_store; balance; drw -l; drf -l; balance; drw -l; drw -z -l; balance; drf -z -l; drw -z -l; balance; fraig_store; fraig_restore;
map -a -D 24000;
buffer -N 64; upsize -D 24000; dnsize -D 26000; stime -p
ABC
cat > synth.ys <<YS
read_slang --top $top -DGF180_SRAM_MACRO -DQSAG_EXTERNAL_SRAM_MODEL -I$rtl -f rtl.f
hierarchy -check -top $top
synth -noabc -top $top
dfflibmap -liberty "$lib" $dont_use qsag_ass2_add64 qsag_ass2_u8add64
abc -liberty "$lib" -constr abc.constr -script fast_add.abc $dont_use qsag_ass2_add64 qsag_ass2_u8add64
setattr -mod -unset keep_hierarchy *
flatten
share
opt -full
techmap -map "$here/gf180_latches.v"
dffunmap w:*u_host* %x
clockgate -min_net_size 4 -pos gf180mcu_fd_sc_mcu7t5v0__icgtp_2 E:CLK:Q -tie_lo TE
techmap
opt -fast
dfflibmap -liberty "$lib" $dont_use
abc -liberty "$lib" -liberty "$ram_lib" -constr abc.constr -script area.abc $dont_use $top
hilomap -hicell gf180mcu_fd_sc_mcu7t5v0__tieh Z -locell gf180mcu_fd_sc_mcu7t5v0__tiel ZN
opt_clean -purge
select -assert-count 1 t:$ram
select -assert-none t:\$*
select -assert-none t:gf180mcu_fd_sc_mcu7t5v0__dffq_* t:gf180mcu_fd_sc_mcu7t5v0__dffnq_* t:gf180mcu_fd_sc_mcu7t5v0__mux2_1 t:gf180mcu_fd_sc_mcu7t5v0__oai33_2 t:gf180mcu_fd_sc_mcu7t5v0__sdff*
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
select -assert-count 1 t:$ram
select -assert-none t:\$*
select -assert-none t:gf180mcu_fd_sc_mcu7t5v0__dffq_* t:gf180mcu_fd_sc_mcu7t5v0__dffnq_* t:gf180mcu_fd_sc_mcu7t5v0__mux2_1 t:gf180mcu_fd_sc_mcu7t5v0__oai33_2 t:gf180mcu_fd_sc_mcu7t5v0__sdff*
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
    if grep -Eq '^(Error:|Warning:.*(black box|not found))|VIOLATED|^worst slack (max|min) -' "sta-$corner.log"; then
        echo "STA failed on corner $corner" >&2
        exit 1
    fi
done
mkdir -p "$here/results/gf180"
rm -f "$here/results/gf180"/sta-amap-*.log
cp -f standard_cells.stat rtl.sha256 mapped.sha256 sta-ss_125C_4v50.log sta-tt_025C_5v00.log sta-ff_n40C_5v50.log "$here/results/gf180/"
cat standard_cells.stat
