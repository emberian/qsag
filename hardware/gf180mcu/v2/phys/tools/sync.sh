#!/bin/sh
# Mac -> hbox: copy what the proxy flow reads into hbox:/var/tmp/fable-dregg180-phys/proj (container: /work/proj).
# Read-only on the repository. Usage: v2/phys/tools/sync.sh [host]
set -eu
H=${1:-hbox}; R=/var/tmp/fable-dregg180-phys/proj
G=$(cd "$(dirname "$0")/../../.." && pwd)        # hardware/gf180mcu
ssh $H "mkdir -p $R/v2/phys $R/librelane"
rsync -a --delete --exclude generated_defines.svh $G/src $G/rtl $G/ip $G/scripts $G/model $H:$R/
rsync -a $G/librelane/slots $G/librelane/macros $G/librelane/pdn $G/librelane/config.yaml \
         $G/librelane/chip_top.sdc $G/librelane/list_steps.py $G/librelane/gf180mcu_render.lyp $H:$R/librelane/
rsync -a --delete --exclude results --exclude __pycache__ --exclude 'px_rom.sv' --exclude 'qsag_p2_rc.sv' $G/v2/phys/ $H:$R/v2/phys/
ssh $H "cp $R/v2/phys/flow/config_phys.yaml $R/v2/phys/flow/chip_top_phys.sdc $R/librelane/"
