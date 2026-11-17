#!/bin/sh
# Runs inside the container dev shell, cwd anywhere. LibreLane `Chip` flow on the proxy from synthesis to the
# step given (default: Odb.AddRoutingObstructions = pad ring, tap cells and PDN in place, nothing placed).
#   run_ll.sh <run-tag> [<last-step>]
set -u
TAG=$1; LAST=${2:-Odb.AddRoutingObstructions}
cd /work/proj
ulimit -v 23000000
{ echo '// generated'; echo '`define SLOT_0P5X0P5'; echo '`define SRAM_gf180mcu_fd_ip_sram'; } > src/generated_defines.svh
[ -f v2/phys/proxy/px_rom.sv ] || python3 v2/phys/proxy/gen_rom.py 1700 28 ucode > v2/phys/proxy/px_rom.sv
[ -f v2/phys/proxy/qsag_p2_rc.sv ] || python3 scripts/gen_p2_rc.py v2/phys/proxy/qsag_p2_rc.sv > /dev/null
rm -rf librelane/runs/$TAG
SRAM_DEFINE=SRAM_gf180mcu_fd_ip_sram librelane \
    librelane/slots/slot_0p5x0p5.yaml librelane/macros/macros_qsag.yaml librelane/config.yaml librelane/config_phys.yaml \
    --pdk gf180mcuD --pdk-root /work/pdk --manual-pdk --scl gf180mcu_fd_sc_mcu7t5v0 --pad gf180mcu_fd_io \
    --run-tag $TAG \
    --skip Verilator.Lint --skip Checker.LintTimingConstructs --skip Checker.LintErrors --skip Checker.LintWarnings \
    --skip Checker.YosysUnmappedCells --skip Checker.NetlistAssignStatements --to $LAST
echo "LL_RC=$?"
