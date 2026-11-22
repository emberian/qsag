#!/usr/bin/env bash
set -euo pipefail

# End-to-end verification script for qsagFpgaTagGate64 on 7x32 FABulous fabric (W_IO8 + 6x30 LUT4AB).
# Run on bb2 with Lean sysroot and OSS CAD Suite on PATH.

PROJ=${PROJ:-/home/build/wave-e12-obend/fabulous_gl64/proj}
BIN=${BIN:-$PROJ/user_design/qsag_fpga_tag_gate64.bin}
WORK=${WORK:-/home/build/wave-e12-obend/fabulous_gl64}
TMP=${TMPDIR:-/home/build/wave-e12-obend/tmp/worker_c}

echo "=== 1. Tile-level agreement & Yosys/Z3 LEC ==="
lean --run "$TMP/fab_cli.lean" tile-agree --project "$PROJ"
for t in lut4ab_sm wio8_sm lut4c mux8lut; do
  cat "$TMP/tile_lec/${t}.fab.smt2" "$TMP/tile_lec/${t}.lean.smt2" > "$TMP/tile_lec/${t}.miter.smt2"
  echo "tile-lec $t: $(z3 "$TMP/tile_lec/${t}.miter.smt2" 2>&1 | sed -n '1p')"
done

echo "=== 2. Compile kernel-checked Lean modules ==="
lean -E error /home/build/wave-e12-obend/lean/Obend/Hardware/Fabulous/TagGate64Bin.lean
lean -E error /home/build/wave-e12-obend/lean/Obend/Hardware/Fabulous/TagGate64Net.lean
lean -E error /home/build/wave-e12-obend/lean/Obend/Hardware/Fabulous/TagGate64Cert.lean

echo "=== 3. Planted fault refusals ==="
lean --run "$TMP/fab_cli.lean" cert --module gl64_tag_gate --project "$PROJ" --bin "$BIN" --mutant
SITE=$(grep -m1 -o '"X[0-9]*Y[0-9]*\.[A-H]"' /home/build/wave-e12-obend/lean/Obend/Hardware/Fabulous/TagGate64Net.lean | tr -d '"')
lean --run "$TMP/fab_cli.lean" flip --project "$PROJ" --bin "$BIN" --feature "${SITE}.INIT[3]" --out "$TMP/flipped_lut.bin"
if lean --run "$TMP/fab_cli.lean" check --module gl64_tag_gate --project "$PROJ" --bin "$TMP/flipped_lut.bin" --golden "$BIN"; then
  echo "[FAIL] flipped LUT accepted"; exit 1
fi
RSITE=$(grep -m1 -oE '#16, \((\.pin|\.ff|\.gate) [0-9]+\), .*"X[0-9]+Y[0-9]+\.[A-H]"' /home/build/wave-e12-obend/lean/Obend/Hardware/Fabulous/TagGate64Net.lean | grep -oE '"X[0-9]+Y[0-9]+\.[A-H]"' | tr -d '"')
NODE="${RSITE%%.*}.L${RSITE##*.}_I0"
lean --run "$TMP/fab_cli.lean" flip --project "$PROJ" --bin "$BIN" --node "$NODE" --out "$TMP/flipped_route.bin"
if lean --run "$TMP/fab_cli.lean" check --module gl64_tag_gate --project "$PROJ" --bin "$TMP/flipped_route.bin" --golden "$BIN"; then
  echo "[FAIL] flipped route accepted"; exit 1
fi

echo "=== 4. 256-cycle configured eFPGA_top simulation (Icarus + Verilator) ==="
vvp "$TMP/tb.vvp" +bitstream_hex="$TMP/bit.hex" +bitbytes=$(wc -c < "$BIN" | tr -d ' ') +vectors="$WORK/vec.hex" +cycles=256
"$TMP/verilator_build_o0/VtagGate64_fabric_tb" +bitstream_hex="$TMP/bit.hex" +bitbytes=$(wc -c < "$BIN" | tr -d ' ') +vectors="$WORK/vec.hex" +cycles=256
