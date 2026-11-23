#!/usr/bin/env bash
set -euo pipefail
[[ $(uname -s) == Linux ]] || { echo "Run on a Linux host" >&2; exit 2; }
here=$(cd "$(dirname "$0")" && pwd)
rtl=$(cd "$here/../rtl" && pwd)
export PATH="${OSS_CAD_BIN:-/opt/oss-cad-suite/bin}:$HOME/.cargo/bin:$PATH"
source "$here/../synth/rtl_sources.sh"

work=$(mktemp -d "${TMPDIR:-/tmp}/ass2-cov.XXXXXX")
trap 'rm -rf "$work"' EXIT
mkdir -p "$work/cov" "$here/coverage_report"

echo "[1/5] PUF + BCH + FIPS bist_allow hard-gate + UART/TRNG health-fault coverage run..."
verilator --coverage-line -DASS2_FAST_ENTROPY --cc --exe --build -j "${JOBS:-6}" -Wall \
    --top-module dregg_ro_puf_bch --Mdir "$work/obj_bch" -I"$rtl" \
    "$rtl/dregg_ro_puf_bch.sv" "$here/sim_bch.cpp" >/dev/null
(cd "$work/obj_bch" && ./Vdregg_ro_puf_bch && mv coverage.dat "$work/cov/bch.dat")

cat > "$work/mock_ring.sv" <<'SV'
module qsag_ass2_ring #(parameter int STAGES = 17) (
    input  wire en,
    output wire osc
);
    assign osc = en && ((STAGES == 33) ? $root.uart_trng_tb.tb_osc_f : $root.uart_trng_tb.tb_sclk);
endmodule
SV
cat > "$work/uart_trng_tb.sv" <<'SV'
module uart_trng_tb (
    input  logic        clk,
    input  logic        rst_n,
    input  logic        dbg_enable,
    input  logic [11:0] clk_div,
    input  logic        tx_we,
    input  logic [7:0]  tx_byte,
    output logic        tx,
    output logic        tx_overflow,
    input  logic        rx,
    input  logic        rx_ack,
    output logic [7:0]  rx_byte,
    output logic        rx_valid,
    input  logic        tb_osc_f,
    input  logic        tb_sclk,
    input  logic        take,
    output logic [63:0] word,
    output logic        valid,
    output logic        ok,
    output logic        rct_fail,
    output logic        apt_fail,
    output wire         raw_bit
);
    qsag_ass2_uart u_uart (.*);
    qsag_trng u_trng (
        .clk(clk), .rst_n(rst_n), .en(1'b1), .take(take),
        .word(word), .valid(valid), .ok(ok),
        .rct_fail(rct_fail), .apt_fail(apt_fail), .raw_bit(raw_bit)
    );
endmodule
SV
verilator --coverage-line --cc --exe --build -j "${JOBS:-6}" -Wall -Wno-DECLFILENAME \
    --top-module uart_trng_tb --Mdir "$work/obj_ut" -I"$rtl" \
    "$work/mock_ring.sv" "$rtl/qsag_ass2_uart.sv" "$rtl/qsag_trng.sv" "$work/uart_trng_tb.sv" "$here/sim_uart_trng.cpp" >/dev/null
(cd "$work/obj_ut" && ./Vuart_trng_tb && mv coverage.dat "$work/cov/ut.dat")

echo "[2/5] Lockstep 1,028-program ISA + crypto cosim coverage run..."
vectors="$work/suite.vec"
firmware=()
for name in canopy cth jive sumcheck; do
    firmware+=(--firmware "$here/firmware_kats/$name.bin")
done
python3 "$here/ass2_model.py"
python3 "$here/gen_cosim_vectors.py" "$vectors" "${firmware[@]}"
verilator --coverage-line -Wno-UNOPTFLAT -DASS2_FAST_ENTROPY --cc --exe --build -j "${JOBS:-6}" \
    --top-module ass2_cosim_top --Mdir "$work/obj_cosim" -I"$rtl" \
    "${rtl_sources[@]}" "$here/ass2_cosim_top.sv" "$here/sim_ass2_lockstep.cpp" >/dev/null
(cd "$work/obj_cosim" && ./Vass2_cosim_top "$vectors" && mv coverage.dat "$work/cov/cosim.dat")

echo "[3/5] Full Enclave lifecycle + FIPS POST KAT + peripheral/lockout coverage run..."
verilator --coverage-line -Wall -Wno-UNOPTFLAT -Wno-SYNCASYNCNET -DASS2_FAST_ENTROPY --cc --exe --build -j "${JOBS:-6}" -O2 -LDFLAGS "-lcrypto" \
    --top-module qsag_ass2_enclave_top --Mdir "$work/obj_enc" -I"$rtl" \
    "${rtl_sources[@]}" "$here/sim_enclave_top.cpp" -o "$work/obj_enc/sim_enclave_top" >/dev/null
(cd "$work/obj_enc" && ./sim_enclave_top | tee "$work/enc.results" && mv coverage.dat "$work/cov/enclave.dat")
python3 -B "$here/check_resident.py" "$work/enc.results"

echo "[4/5] Negative FIPS 140-3 §10.3.A Cold-Boot POST KAT mismatch lockout run..."
verilator --coverage-line -Wall -Wno-UNOPTFLAT -Wno-SYNCASYNCNET -DASS2_FAST_ENTROPY -GPOST_KAT_GOLDEN=64\'hdead_beef_cafe_f00d \
    -CFLAGS "-DTEST_POST_KAT_FAIL=1" --cc --exe --build -j "${JOBS:-6}" -O2 -LDFLAGS "-lcrypto" \
    --top-module qsag_ass2_enclave_top --Mdir "$work/obj_postfail" -I"$rtl" \
    "${rtl_sources[@]}" "$here/sim_enclave_top.cpp" -o "$work/obj_postfail/sim_postfail" >/dev/null
(cd "$work/obj_postfail" && ./sim_postfail && mv coverage.dat "$work/cov/postfail.dat")

echo "[5/5] Merging & computing exact RTL line coverage..."
rm -rf "$here/coverage_report/annotated"
verilator_coverage --write "$here/coverage_report/merged.dat" "$work"/cov/*.dat
verilator_coverage --annotate "$here/coverage_report/annotated" --annotate-all "$here/coverage_report/merged.dat" > "$here/coverage_report/verilator_cov.txt"
python3 - "$here/coverage_report/annotated" <<'PY' | tee "$here/coverage_report/summary.txt"
import re, sys
from pathlib import Path
ann = Path(sys.argv[1])
tot_hit = tot_all = 0
print(f"{'RTL File':<36} {'Hit':>6} / {'Total':<6} {'Coverage':>8}")
print("-" * 62)
for p in sorted(ann.glob("*.sv")):
    if p.name in ("ass2_cosim_top.sv", "gf180mcu_fd_ip_sram__sram512x8m8wm1.sv", "uart_trng_tb.sv", "mock_ring.sv"):
        continue
    hit = miss = 0
    for line in p.read_text().splitlines():
        m = re.match(r"^([%~ ]?)(\d{6})\s", line)
        if m:
            cnt = int(m.group(2))
            if cnt > 0: hit += 1
            else: miss += 1
    n = hit + miss
    if n == 0: continue
    tot_hit += hit; tot_all += n
    print(f"{p.name:<36} {hit:>6} / {n:<6} {100.0*hit/n:>7.2f}%")
print("-" * 62)
pct = 100.0 * tot_hit / max(tot_all, 1)
print(f"{'TOTAL PRODUCTION RTL':<36} {tot_hit:>6} / {tot_all:<6} {pct:>7.2f}%")
if pct < 95.0:
    print(f"NOTE: Below 95.0% target ({pct:.2f}%) — inspect uncovered lines in coverage_report/annotated/")
PY
