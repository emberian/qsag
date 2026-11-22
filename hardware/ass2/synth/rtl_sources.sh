# Source after setting rtl to the absolute ASS2 RTL directory.
# Both Slang and Verilator require packages before their consumers.
rtl_sources=("$rtl/qsag_ass2_pkg.sv")
for src in "$rtl"/*.sv; do
    [[ "$src" == "${rtl_sources[0]}" ]] || rtl_sources+=("$src")
done
