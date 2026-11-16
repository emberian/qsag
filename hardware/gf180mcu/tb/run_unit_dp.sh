#!/bin/sh
# Datapath unit test (run remotely, cwd = project root).
set -e
mkdir -p build
python3 scripts/gen_p2_rc.py rtl/qsag_p2_rc.sv
python3 tb/gen_dp_vectors.py tb/fixtures/lean_external_oracle_vectors.json build/dp_vectors.txt
RTL="rtl/qsag_cells.sv rtl/qsag_gl64_karatsuba_csa.sv rtl/qsag_sponge.sv rtl/qsag_p2_rc.sv rtl/qsag_field_engine.sv tb/dp_top.sv"
for cfg in "" "-DQSAG_ICG"; do
    rm -rf build/obj_dp
    verilator --cc --exe --build -j 8 -Wall -Wno-fatal $cfg --top-module dp_top -Mdir build/obj_dp \
        $RTL tb/unit_dp.cpp -o unit_dp > build/unit_dp_build.log 2>&1 || { tail -40 build/unit_dp_build.log; exit 1; }
    grep -c '%Warning' build/unit_dp_build.log || true
    echo "config: [$cfg]"
    build/obj_dp/unit_dp build/dp_vectors.txt
done
