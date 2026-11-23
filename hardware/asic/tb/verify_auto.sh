#!/usr/bin/env bash
# Reproduce D1 in the dedicated checkout. Named gates can be rerun independently.
set -euo pipefail
root=$(cd "$(dirname "$0")/../../.." && pwd)
cd "$root/hardware/asic"
export TMPDIR="$root/work_tmp"
OSS_CAD_BIN=${OSS_CAD_BIN:-/opt/oss-cad-suite/bin}
export PATH="$OSS_CAD_BIN:${OPENROAD_BIN:-/opt/openroad/bin}:$HOME/.cargo/bin:$HOME/.local/bin:$PATH"
export CARGO_TARGET_DIR="$TMPDIR/fixture-target" CARGO_BUILD_JOBS="${JOBS:-3}" QSAG_WORKERS="${JOBS:-3}"
mkdir -p "$TMPDIR" synth/logs
log=synth/logs
bin="$CARGO_TARGET_DIR/release"
sim=${AUTO_SIM:-$TMPDIR/auto/sim}
gate() {
  case "$1" in
    rom) /usr/bin/python3 rtl/auto/build.py | tee "$log/rom_build.log" ;;
    fixtures)
      cargo build --release --manifest-path tb/rust/auto/Cargo.toml --bins
      "$bin/fixture" >"$log/fixture.log"
      "$bin/hqm_fixture" >"$log/hqm_fixture.log"
      "$bin/hqm_fixture" --multi >"$log/hqm_multi_fixture.log"
      "$bin/mutations" >"$log/mutations.log"
      for f in v2 hqm2 hqm2_multi; do
        echo "$f"
        "$bin/rom_ref" "vec/proof_$f.bin" "vec/statement_$f.bin"
      done >"$log/rom_ref.log"
      sha256sum rtl/auto/verifier.hex rtl/qsag_auto_rom{.sv,_size.svh} \
        vec/{proof,statement}_{v2,hqm2,hqm2_multi}.bin vec/tamper_{v2,hqm2}.txt >"$log/artifacts.sha256" ;;
    lint) bash tb/run.sh lint >"$log/lint.log" 2>&1 ;;
    bram)
      for arch in xilinx ecp5; do
        if [[ $arch == xilinx ]]; then
          flow='synth_xilinx -family xcup'
          cell=RAMB36E2; count=8
        else
          flow=synth_ecp5
          cell=DP16KD; count=16
        fi
        # Deliberately elaborate from outside the RTL source tree.
        (cd "$TMPDIR" && yosys -Q -T -p "read_verilog -sv $root/hardware/asic/rtl/qsag_auto_rom.sv; $flow -top qsag_auto_rom; select -assert-count $count t:$cell; select -assert-none t:LUT*; stat") >"$log/bram_$arch.log" 2>&1
      done ;;
    command)
      bash tb/run.sh tb_units >"$log/tb_units.log" 2>&1
      HIERARCHICAL=1 bash tb/run.sh tb_top >"$log/tb_top_post_h2.log" 2>&1
      HIERARCHICAL=1 bash tb/run.sh tb_zkhem_v2_top >"$log/tb_zkhem_v2.log" 2>&1 ;;
    formal)
      for mode in shared fp5; do /usr/bin/python3 lec/miter.py "$mode" >"$log/miter_$mode.log"; done
      /usr/bin/python3 lec/auto_miter.py >"$log/auto_miter.log" ;;
    foundry) /usr/bin/python3 -u synth/run_foundry_v2.py | tee "$log/foundry_synth_sta.log" ;;
    build) bash tb/auto_sim.sh tb_auto_v2 "$TMPDIR/auto" >"$log/build_final.log" 2>&1 ;;
    zk|hqm)
      if [[ $1 == zk ]]; then f=v2; else f=hqm2; fi
      "$sim" "+proof=vec/proof_$f.bin" "+desc=vec/statement_$f.bin" \
        "+campaign=vec/tamper_$f.txt" "+workers=${JOBS:-3}" >"$log/auto_$1.log"
      if [[ $1 == zk ]]; then
        python3 tb/campaign_report.py vec/tamper_v2.txt "$log/auto_zk.log" --envelope >"$log/auto_zk_envelope.log"
      else
        python3 tb/campaign_report.py vec/tamper_hqm2.txt "$log/auto_hqm.log" >"$log/auto_hqm_fields.log"
      fi ;;
    multi) "$sim" +proof=vec/proof_hqm2_multi.bin +desc=vec/statement_hqm2_multi.bin +checks=108 >"$log/auto_multi.log" ;;
    tamper)
      for field in committee message; do
        offset=$(/usr/bin/python3 - "$field" <<'PY'
import struct, sys
from pathlib import Path
s = Path("vec/statement_hqm2_multi.bin").read_bytes()
def length(p):
    return struct.unpack_from("<I", s, p)[0]
committee = 12 + length(8) + 4
message = committee + length(committee - 4) + 1 + 4
# In this multi-signer fixture both counts are single-byte canonical LEB128.
assert s[message-5] == 1 and s[message] == 2 and 0 < s[message+1] < 128
print(committee + 1 if sys.argv[1] == "committee" else message + 2)
PY
)
        "$sim" +proof=vec/proof_hqm2_multi.bin +desc=vec/statement_hqm2_multi.bin "+desc_flip=$offset" >"$log/tamper_$field.log"
      done ;;
    edges)
      "$sim" +noncanonical=92 >"$log/auto_noncanonical.log"
      "$sim" +delta=-1 >"$log/auto_truncated.log"
      "$sim" +delta=1 >"$log/auto_trailing.log" ;;
    page) "$sim" +page=4096 >"$log/auto_paged.log" ;;
    page_hqm) "$sim" +page=4096 +proof=vec/proof_hqm2.bin +desc=vec/statement_hqm2.bin >"$log/auto_hqm_paged.log" ;;
    page_multi) "$sim" +page=4096 +proof=vec/proof_hqm2_multi.bin +desc=vec/statement_hqm2_multi.bin +checks=108 >"$log/auto_multi_paged.log" ;;
    *) echo "Unknown gate $1" >&2; return 2 ;;
  esac
}
if [[ $# == 0 ]]; then set -- rom fixtures lint bram command formal build zk hqm multi tamper edges page page_hqm page_multi foundry; fi
for stage; do echo "D1 gate $stage"; gate "$stage"; done
